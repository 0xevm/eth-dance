use std::str::FromStr;

use bigdecimal::{FromPrimitive, num_bigint::BigInt, BigDecimal};
use ethers::types::{Address, I256, U256};

use crate::{
  vm::{Value, ValueKind, ValueKey},
  ast::NumberSuffix,
  typing::Type,
};

use super::{Error, conv::{ErrorKind, ErrorExt}};

pub enum Number {
  I(I256), U(U256), F(Vec<u8>),
}

impl Value {
  pub fn as_bytecode(&self) -> Option<&Vec<u8>> {
    match &self.v {
      ValueKind::Bytecode(v) => Some(v),
      _ => None,
    }
  }
  pub fn as_address(&self) -> Option<Address> {
    match &self.v {
      ValueKind::Address(v) => Some(*v),
      _ => None,
    }
  }
  pub fn as_number(&self) -> Option<(&BigDecimal, NumberSuffix)> {
    match &self {
      Self { v: ValueKind::Number(base), ty: Type::Number(suffix) }
        => Some((base, *suffix)),
      _ => None,
    }
  }
  pub fn as_value_key(&self) -> Option<ValueKey> {
    let key = match &self.v {
      ValueKind::Address(addr) => ValueKey::Address(*addr),
      ValueKind::String(string) => ValueKey::String(string.clone()),
      _ => return None,
    };
    Some(key)
  }
}

impl TryInto<Number> for &Value {
  type Error = Error;

  fn try_into(self) -> Result<Number, Self::Error> {
    match self.as_number() {
      Some((base, suffix)) => {
        trace!("try_from(Value<=TypedNumber): {:?}", suffix);
        match suffix {
          NumberSuffix::None => {
            if !base.is_integer() {
              return Err(ErrorKind::Number("cannot convert raw float to int").context("try_into_number"));
            }
            let v = U256::from_dec_str(&base.to_string()).context("try_into_number")?;
            return Ok(Number::U(v))
          },
          NumberSuffix::Signed => {
            if !base.is_integer() {
              return Err(ErrorKind::Number("cannot convert raw float to int").context("try_into_number"));
            }
            let v = I256::from_dec_str(&base.to_string()).context("try_into_number")?;
            return Ok(Number::I(v))
          }
          _ => {}
        }
        let mut base = base.clone();
        let suffix = suffix.clone();
        match suffix {
          NumberSuffix::Q(_, s) => {
            base *= BigDecimal::from(BigInt::from_usize(1).unwrap() << s);
          }
          // NumberSuffix::F(b, s) => {}
          NumberSuffix::E(_, s) => {
            base *= BigDecimal::from(BigInt::from_usize(10).unwrap().pow(s as u32));
          },
          _ => {}
        }
        let value = match suffix {
          NumberSuffix::Q(true, _) | NumberSuffix::E(true, _) => {
            if base < BigDecimal::from_isize(0).unwrap() {
              return Err(ErrorKind::Number("value < 0")).context("try_into_number")
            }
            if base >= BigDecimal::from(BigInt::from_usize(2).unwrap().pow(256)) {
              return Err(ErrorKind::Number("value >= 2**256")).context("try_into_number")
            }
            trace!("try_from(Value<=TypedNumber): base(u) = {}", base.to_string());
            Number::U(U256::from_dec_str(&base.round(0).to_string()).unwrap())
          },
          NumberSuffix::Q(false, _) | NumberSuffix::E(false, _) => {
            let bound = BigDecimal::from(BigInt::from_usize(2).unwrap().pow(255));
            if base >= bound {
              return Err(ErrorKind::Number("value >= 2**255")).context("try_into_number")
            }
            if base < -bound {
              return Err(ErrorKind::Number("value < -2**255")).context("try_into_number")
            }
            trace!("try_from(Value<=TypedNumber): base(i) = {}", base.to_string());
            Number::I(I256::from_dec_str(&base.round(0).to_string()).unwrap())
          },
          NumberSuffix::F(size) if [32, 64].contains(&size) => {
            let bytes = match size {
              32 => f32::from_str(base.to_string().as_str()).map_err(|_| ErrorKind::Number("f32 convert").context("try_into_number"))?.to_bits().to_be_bytes().to_vec(),
              64 => f64::from_str(base.to_string().as_str()).map_err(|_| ErrorKind::Number("f64 convert").context("try_into_number"))?.to_bits().to_be_bytes().to_vec(),
              _ => unreachable!()
            };
            assert_eq!(bytes.len(), size/8);
            Number::F(bytes)
          },
          NumberSuffix::F(_) => {
            warn!("fixme: ieee");
            todo!("fixme: ieee");
          },
          _ => unreachable!(),
        };
        Ok(value)
      },
      _ => Err(ErrorKind::NotCompatible(format!("not number")).context("try_into_i256"))
    }
  }
}

impl TryInto<f64> for Number {
  type Error = Error;
  fn try_into(self) -> Result<f64, Self::Error> {
    match &self {
      Number::U(i) => return i.to_string().parse::<f64>().map_err(ErrorKind::from).context("try_into_f64"),
      Number::I(i) => return i.to_string().parse::<f64>().map_err(ErrorKind::from).context("try_into_f64"),
      Number::F(i) => {
        match i.len() {
          8 => {
            let mut t = [0u8; 8];
            if i.len() != t.len() {
              return Err(ErrorKind::custom("fixed bytes len mismatch").context("try_into_f64"))
            }
            t.clone_from_slice(i);
            return Ok(f64::from_be_bytes(t))
          }
          4 => {
            let mut t = [0u8; 4];
            if i.len() != t.len() {
              return Err(ErrorKind::custom("fixed bytes len mismatch").context("try_into_f64"))
            }
            t.clone_from_slice(i);
            return Ok(f32::from_be_bytes(t) as _)
          }
          _ => {}
        }
      },
    };
    return Err(ErrorKind::NotCompatible(format!("Number")).context("try_into_f64"))
  }
}
