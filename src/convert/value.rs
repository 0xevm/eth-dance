use std::str::FromStr;

use bigdecimal::FromPrimitive;
use ethabi::{Address, Token, ParamType};
use ethers::types::{U256, I256};

use crate::{
  vm::Value,
  ast::{TypedNumber, NumberSuffix, TypedString},
  typing::Type,
};

use super::{conv::try_convert_hex_to_bytes, Error};

impl From<Address> for Value {
  fn from(value: Address) -> Self {
    Self {
      token: Token::Address(value),
      abi: ParamType::Address,
      ty: None,
    }
  }
}

impl TryFrom<TypedNumber> for Value {
  type Error = &'static str;
  fn try_from(value: TypedNumber) -> Result<Self, Self::Error> {
    let ty = Some(Type::Number(value.suffix));
    trace!("try_from(Value<=TypedNumber): {:?}", ty);
    match value.suffix {
      NumberSuffix::None => {
        if value.value.contains(".") {
          return Err("cannot convert raw float to int")
        }
        let v = U256::from_dec_str(&value.value).map_err(|_| "convert to U256 failed")?;
        return Ok(Value { token: Token::Uint(v), abi: ParamType::Uint(256), ty })
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
        trace!("try_from(Value<=TypedNumber): base(u) = {}", base.to_string());
        Value {
          token: Token::Int(U256::from_dec_str(&base.round(0).to_string()).unwrap()),
          abi: ParamType::Uint(256), ty,
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
        trace!("try_from(Value<=TypedNumber): base(i) = {}", base.to_string());
        Value {
          token: Token::Int(I256::from_dec_str(&base.round(0).to_string()).unwrap().into_raw()),
          abi: ParamType::Int(256), ty,
        }
      },
      NumberSuffix::F(size) if [32, 64].contains(&size) => {
        let bytes = match size {
          32 => f32::from_str(base.to_string().as_str()).map_err(|_| "f32 convert")?.to_bits().to_be_bytes().to_vec(),
          64 => f64::from_str(base.to_string().as_str()).map_err(|_| "f64 convert")?.to_bits().to_be_bytes().to_vec(),
          _ => unreachable!()
        };
        assert_eq!(bytes.len(), size/8);
        Value {
          abi: ParamType::FixedBytes(bytes.len()), ty,
          token: Token::FixedBytes(bytes),
        }
      },
      NumberSuffix::F(_) => {
        warn!("fixme: ieee");
        Value {
          token: Token::Int(I256::zero().into_raw()),
          abi: ParamType::Int(256), ty,
        }
      },
      _ => unreachable!(),
    };
    Ok(value)
  }
}

impl TryFrom<TypedString> for Value {
  type Error = Error;

  fn try_from(value: TypedString) -> std::result::Result<Self, Self::Error> {
    let ty = Some(Type::String(value.prefix.clone()));
    if value.prefix.is_empty() {
      let string = String::from_utf8(value.value)?;
      return Ok(Value {
        token: Token::String(string),
        abi: ParamType::String, ty,
      })
    }
    let prefix = value.prefix;
    let bytes = match prefix.as_str() {
      "hex" | "key" => {
        // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
        try_convert_hex_to_bytes(value.value.as_slice())?
      }
      "address" => {
        let addr = try_convert_hex_to_bytes(value.value.as_slice())?;
        return Ok(Value {
          token: Token::Address(Address::from_slice(&addr)),
          abi: ParamType::Address, ty,
        })
      }
      "b" => {
        value.value
      }
      _ => return Err(Error::UnknownPrefix(prefix)),
    };
    Ok(Value {
      token: Token::Bytes(bytes),
      abi: ParamType::Bytes, ty
    })
  }
}
