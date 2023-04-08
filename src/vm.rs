use std::{collections::BTreeMap, str::FromStr};

use bigdecimal::FromPrimitive;
use ethers::types::{I256, U256, H160, Address};

use crate::{typing::{Typing, ExprT, Id, Type}, ast::{TypedNumber, NumberSuffix, TypedString}};

// pub struct Error {

// }
// pub type Result<T, E=Error> = std::result::Result<T, E>;
pub use anyhow::Result;

#[derive(Debug, Clone)]
pub struct Value {
  pub value: ethabi::Token,
  pub abi: ethabi::ParamType,
  pub ty: Option<Type>,
}

impl From<Address> for Value {
  fn from(value: Address) -> Self {
    Self {
      value: ethabi::Token::Address(value),
      abi: ethabi::ParamType::Address,
      ty: None,
    }
  }
}

impl TryFrom<TypedNumber> for Value {
  type Error = &'static str;
  fn try_from(value: TypedNumber) -> Result<Self, Self::Error> {
    let ty = Some(Type::Number(value.suffix));
    trace!("try_from: {:?}", ty);
    match value.suffix {
      NumberSuffix::None => {
        if value.value.contains(".") {
          return Err("cannot convert raw float to int")
        }
        let v = U256::from_dec_str(&value.value).map_err(|_| "convert to U256 failed")?;
        return Ok(Value { value: ethabi::Token::Uint(v), abi: ethabi::ParamType::Uint(256), ty })
      },
      _ => {}
    }
    let mut base = bigdecimal::BigDecimal::from_str(&value.value).map_err(|_| "convert to BigDecimal failed")?;
    match value.suffix {
      NumberSuffix::Q(b, s) => {
        base *= bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(1).unwrap() << s);
      }
      NumberSuffix::F(b, s) => {}
      NumberSuffix::D(b, s) => {
        trace!("10^{} = {}", s, bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(10).unwrap().pow(s as u32)).to_string());
        base *= bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(10).unwrap().pow(s as u32));
      },
      _ => {}
    }
    let value = match value.suffix {
      NumberSuffix::Q(true, _) | NumberSuffix::D(true, _) => {
        if base < bigdecimal::BigDecimal::from_isize(0).unwrap() {
          return Err("value < 0")
        }
        if base >= bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(2).unwrap().pow(256)) {
          return Err("value >= 2**256")
        }
        trace!("{}", base.to_string());
        Value {
          value: ethabi::Token::Int(U256::from_dec_str(&base.round(0).to_string()).unwrap()),
          abi: ethabi::ParamType::Uint(256), ty,
        }
      },
      NumberSuffix::Q(false, _) | NumberSuffix::D(false, _) => {
        let bound = bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(2).unwrap().pow(255));
        if base >= bound {
          return Err("value >= 2**255")
        }
        if base < -bound {
          return Err("value < -2**255")
        }
        trace!("{}", base.to_string());
        Value {
          value: ethabi::Token::Int(I256::from_dec_str(&base.round(0).to_string()).unwrap().into_raw()),
          abi: ethabi::ParamType::Int(256), ty,
        }
      },
      NumberSuffix::F(_, _) => {
        warn!("fixme: ieee");
        Value {
          value: ethabi::Token::Int(I256::zero().into_raw()),
          abi: ethabi::ParamType::Int(256), ty,
        }
      },
      _ => unreachable!(),
    };
    Ok(value)
  }
}

impl TryFrom<TypedString> for Value {
  type Error = &'static str;

  fn try_from(value: TypedString) -> std::result::Result<Self, Self::Error> {
    let ty = Some(Type::String(value.prefix.clone().unwrap_or_default()));
    if value.prefix.is_none() {
      return Ok(Value {
        value: ethabi::Token::Bytes(value.value),
        abi: ethabi::ParamType::Bytes, ty,
      })
    }
    let prefix = value.prefix.unwrap();
    let bytes = match prefix.as_str() {
      "hex" => {
        // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
        let mut input = value.value.as_slice();
        if input.starts_with("0x".as_bytes()) {
          input = &input[2..];
        }
        hex::decode(input).map_err(|e| {
          error!("FromHexError: {:?}", e);
          "decode hex"
        })?
      }
      "key" => {
        warn!("fixme: private key");
        value.value
      }
      _ => return Err("unknown prefix"),
    };
    Ok(Value {
      value: ethabi::Token::Bytes(bytes),
      abi: ethabi::ParamType::Bytes, ty
    })
  }
}

pub struct VM {
  pub values: BTreeMap<Id, Value>,
}

impl VM {
  pub fn new() -> Self {
    Self {
      values: Default::default(),
    }
  }
  pub fn set_value(&mut self, id: Id, ty: Type, value: Value) -> Result<()> {
    let value = try_convert(ty, value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    self.values.insert(id, value);
    Ok(())
  }
}

pub fn try_convert(ty: Type, mut value: Value) -> Result<Value, &'static str> {
  if Some(&ty) == value.ty.as_ref() {
    return Ok(value)
  }
  let value = match (&ty, &value.abi) {
    (Type::ContractType(_), ethabi::ParamType::Bytes) |
    (Type::Contract(_), ethabi::ParamType::Address) |
    (Type::Number(_), ethabi::ParamType::Int(_)) |
    (Type::Number(_), ethabi::ParamType::Uint(_)) |
    (Type::String(_), ethabi::ParamType::Bytes)
      => {
        value.ty = Some(ty);
        value
      },
    _ => {
      warn!("fixme: convert to ty: {:?} => {:?}", value.ty, ty);
      value
    }
  };
  Ok(value)
}

pub fn execute(vm: &mut VM, typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    match &info.expr.t {
      ExprT::None => {
        warn!("expr is none: {:?}", id)
      }
      ExprT::Expr(i) => {
        let value = if let Some(value) = vm.values.get(i) {
          value.clone()
        } else {
          anyhow::bail!("vm: copy value from {:?} failed", i);
        };
        vm.set_value(*id, info.ty().clone(), value)?;
      }
      ExprT::Func { func, this, args, send } => {
        if func.ns == "@Global" && func.name == "deploy" && args.len() == 1 {
          let contract_name = match typing.get_info_view(args.get(0).copied().unwrap()).ty() {
            Type::ContractType(name) => name,
            t => {
              anyhow::bail!("vm: deploy args not contract {:?}", t)
            }
          };
          trace!("contract name {}", contract_name);
          let bytecode = match vm.values.get(&args[0]) {
            Some(Value { value: ethabi::Token::Bytes(bytes), ..}) => bytes,
            _ => anyhow::bail!("vm: contract bytecode not present"),
          };
          let result = deploy_contract(contract_name, bytecode)?;
          vm.set_value(*id, info.ty().clone(), result.into())?;
        } else {
          warn!("fixme: send tx");
        }
      }
      ExprT::Number(number) => {
        let value = Value::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?;
        vm.set_value(*id, info.ty().clone(), value)?;
      }
      ExprT::String(string) => {
        let value = Value::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?;
        vm.set_value(*id, info.ty().clone(), value)?;
      }
      // _ => {
      //   warn!("skip {:?} => {:?}", id, info.expr.returns)
      // }
    }
  }
  Ok(())
}

fn deploy_contract(contract_name: &str, bytecode: &[u8]) -> Result<Address> {
  info!("deploy_contract: {} {}", contract_name, bytecode.len());
  warn!("fixme: deploy");
  Ok(Address::default())
}
