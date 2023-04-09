use std::{collections::BTreeMap, str::FromStr};

use bigdecimal::FromPrimitive;
use ethabi::{Token, ParamType};
use ethers::{types::{I256, U256, H256, Address, TransactionRequest, TransactionReceipt}, providers::Middleware, signers::{LocalWallet, Signer}};

use crate::{
  typing::{Typing, ExprCode, Id, Type, Info},
  ast::{TypedNumber, NumberSuffix, TypedString},
  abi::Func
};

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
      NumberSuffix::Q(_, s) => {
        base *= bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(1).unwrap() << s);
      }
      // NumberSuffix::F(b, s) => {}
      NumberSuffix::E(_, s) => {
        trace!("10^{} = {}", s, bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(10).unwrap().pow(s as u32)).to_string());
        base *= bigdecimal::BigDecimal::from(bigdecimal::num_bigint::BigInt::from_usize(10).unwrap().pow(s as u32));
      },
      _ => {}
    }
    let value = match value.suffix {
      NumberSuffix::Q(true, _) | NumberSuffix::E(true, _) => {
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
      NumberSuffix::Q(false, _) | NumberSuffix::E(false, _) => {
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
      let string = String::from_utf8(value.value).map_err(|_| "utf8")?;
      return Ok(Value {
        value: ethabi::Token::String(string),
        abi: ethabi::ParamType::String, ty,
      })
    }
    let prefix = value.prefix.unwrap();
    let bytes = match prefix.as_str() {
      "hex" | "key" => {
        // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
        try_convert_hex_to_bytes(value.value.as_slice())?
      }
      "address" => {
        let addr = try_convert_hex_to_bytes(value.value.as_slice())?;
        return Ok(Value {
          value: Token::Address(Address::from_slice(&addr)),
          abi: ParamType::Address, ty,
        })
      }
      "b" => {
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

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;
pub struct VM {
  pub values: BTreeMap<Id, Value>,
  pub builtin: BTreeMap<String, Value>,
  pub wallet: Option<LocalWallet>,
  pub confirm_interval: Option<f64>,
  pub provider: Provider,
}

impl VM {
  pub fn new() -> Self {
    Self {
      values: Default::default(),
      builtin: Default::default(),
      wallet: None,
      confirm_interval: None,
      provider: Provider::try_from("http://localhost:8545").unwrap(),
    }
  }
  pub fn set_builtin(&mut self, name: &str, value: &Value) {
    match name {
      "$endpoint" => match &value.value {
        Token::String(s) => {
          *self.provider.url_mut() = url::Url::parse(s).unwrap();
        }
        _ => unreachable!()
      }
      "$account" => match &value.value {
        Token::Bytes(bytes) => {
          self.wallet = Some(LocalWallet::from_bytes(bytes).unwrap());
        }
        _ => unreachable!()
      }
      "$confirm_interval" => match &value.value {
        Token::Uint(i) => {
          self.confirm_interval = Some(i.as_u64() as _)
        }
        _ => unreachable!()
      }
      _ => warn!("unknown builtin name {}", name)
    };
    self.builtin.insert(name.to_string(), value.clone());
  }
  pub fn set_value(&mut self, id: Id, info: &Info, value: Value) -> Result<()> {
    trace!("set_value: {:?} = {}", id, value.value);
    let value = try_convert(info.ty(), value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    if info.display.starts_with("$") && !info.display.starts_with("$$") {
      self.set_builtin(&info.display, &value);
    }
    self.values.insert(id, value);
    Ok(())
  }
  pub fn get_address(&self, id: Id) -> Option<Address> {
    match self.values.get(&id)?.value {
      Token::Address(addr) => Some(addr),
      _ => None,
    }
  }
}

pub fn try_convert_hex_to_bytes(mut input: &[u8]) -> Result<Vec<u8>, &'static str> {
  // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
  if input.starts_with("0x".as_bytes()) {
    input = &input[2..];
  }
  let result = hex::decode(input).map_err(|e| {
    error!("FromHexError: {:?}", e);
    "decode hex"
  })?;
  Ok(result)
}

pub fn try_convert_u256_to_h256(i: U256) -> H256 {
  let mut bytes = [0u8; 32];
  i.to_big_endian(&mut bytes);
  H256::from(bytes)
}

pub fn try_convert(ty: &Type, mut value: Value) -> Result<Value, &'static str> {
  if Some(ty) == value.ty.as_ref() {
    return Ok(value)
  }
  let mut value = match (ty, &value.abi) {
    (Type::ContractType(_), ethabi::ParamType::Bytes) |
    (Type::Contract(_), ethabi::ParamType::Address) |
    (Type::Number(_), ethabi::ParamType::Int(_)) |
    (Type::Number(_), ethabi::ParamType::Uint(_)) |
    (Type::String(_), ethabi::ParamType::Bytes)
      => {
        value
      },
    (Type::Contract(_), ethabi::ParamType::Uint(_))
      => {
        let new_value: Address = match value.value {
          Token::Uint(i) | Token::Int(i) =>
            try_convert_u256_to_h256(i).into(),
          _ => unreachable!(),
        };
        value.value = Token::Address(new_value);
        value.abi = ParamType::Address;
        value
      }
    (Type::NoneType, _) => {
      value.value = Token::FixedBytes(vec![]);
      value.abi = ParamType::FixedBytes(0);
      value
    }
    _ => {
      warn!("fixme: convert to ty: {:?} => {:?}", value.abi, ty);
      value
    }
  };
  value.ty = Some(ty.clone());
  Ok(value)
}

pub fn execute(vm: &mut VM, typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    match &info.expr.code {
      ExprCode::None => {
        warn!("expr is none: {:?}", id)
      }
      ExprCode::Expr(i) => {
        let value = if let Some(value) = vm.values.get(i) {
          value.clone()
        } else {
          anyhow::bail!("vm: copy value from {:?} failed", i);
        };
        vm.set_value(*id, info, value)?;
      }
      ExprCode::Func { func, this, args, send } => {
        let args = args.iter().map(|i| vm.values.get(i)).collect::<Option<Vec<_>>>().ok_or_else(|| anyhow::format_err!("vm: args no present"))?;
        if func.ns == "@Global" && func.name == "deploy" && *send {
          let this = this.unwrap();
          let contract_name = match typing.get_info_view(this).ty() {
            Type::ContractType(name) => name,
            t => {
              anyhow::bail!("vm: deploy args not contract {:?}", t)
            }
          };
          trace!("contract name {}", contract_name);
          let bytecode = match vm.values.get(&this) {
            Some(Value { value: ethabi::Token::Bytes(bytes), ..}) => bytes,
            _ => anyhow::bail!("vm: contract bytecode not present"),
          };
          let result = deploy_contract(vm, contract_name, bytecode, &args)?;
          vm.set_value(*id, info, result.unwrap().into())?;
        } else if func.ns.starts_with("@") {
          let result = call_global(vm, func.clone(), &args)?;
          vm.set_value(*id, info, result)?;

        } else if let Some(this) = this {
          trace!("this_addr: {:?} {:?} {:?}", id, this, vm.get_address(*this));
          let this_addr = vm.get_address(*this).ok_or_else(|| anyhow::format_err!("vm: this not address"))?;
          let result = if *send {
            send_tx(vm, this_addr, func.clone(), &args)?
          } else {
            call_tx(vm, this_addr, func.clone(), &args)?
          };
          vm.set_value(*id, info, result)?;
        } else {
          unreachable!()
        }
      }
      ExprCode::Number(number) => {
        let value = Value::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?;
        vm.set_value(*id, info, value)?;
      }
      ExprCode::String(string) => {
        let value = Value::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?;
        vm.set_value(*id, info, value)?;
      }
      // _ => {
      //   warn!("skip {:?} => {:?}", id, info.expr.returns)
      // }
    }
  }
  Ok(())
}

fn call_global(_vm: &VM, func: Func, args: &[&Value]) -> Result<Value> {
  let out = match (func.ns.as_str(), func.name.as_str()) {
    ("@assert", "eq") => {
      if args[0].value != args[1].value {
        anyhow::bail!("vm: assert_eq failed: {} != {}", args[0].value, args[1].value)
      }
      vec![]
    }
    _ => unreachable!()
  };
  Ok(func.to_output(out))
}

#[tokio::main]
async fn do_send_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<Option<TransactionReceipt>> {
  if let Some(wallet) = &vm.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  let pending = vm.provider.send_transaction(tx, None).await?;
  trace!("pending: {:?}", pending);
  let pending = if let Some(i) = vm.confirm_interval {
    pending.interval(std::time::Duration::from_secs_f64(i))
  } else {
    pending
  };
  Ok(pending.await?)
}

#[tokio::main]
async fn do_call_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<ethabi::Bytes> {
  if let Some(wallet) = &vm.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  Ok(vm.provider.call(&tx.into(), None).await?.to_vec())
}

fn send_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value]) -> Result<Value> {
  let tokens = args.iter().map(|i| i.value.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  do_send_tx_sync(vm, tx)?;
  Ok(Value {
    value: Token::Uint(U256::zero()),
    abi: ethabi::ParamType::Uint(256),
    ty: None,
  })
}

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value]) -> Result<Value> {
  let tokens = args.iter().map(|i| i.value.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let bytes = do_call_tx_sync(vm, tx)?;
  let out = ethabi::decode(&func.output_types, &bytes)?;
  let result = func.to_output(out);
  // vm.provider.
  Ok(result)
}

fn deploy_contract(vm: &VM, contract_name: &str, bytecode: &[u8], args: &[&Value]) -> Result<Option<Address>> {
  let tokens = args.iter().map(|i| i.value.clone()).collect::<Vec<_>>();
  info!("deploy_contract: {} {} to {}", contract_name, bytecode.len(), vm.provider.url());
  let mut input_data = Vec::new();
  input_data.extend_from_slice(bytecode);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  let tx = TransactionRequest::new().data(input_data);//.from(vm.builtin.account);
  let receipt = do_send_tx_sync(vm, tx)?;
  let address = receipt.and_then(|i| i.contract_address);
  Ok(address)
}
