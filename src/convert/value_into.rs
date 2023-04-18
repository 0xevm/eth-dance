use ethabi::Token;
use ethers::types::I256;

use crate::{vm::EvmValue, typing::Type, ast::NumberSuffix};

use super::{Error, conv::{ErrorKind, ErrorKindExt}};

impl TryInto<f64> for &EvmValue {
  type Error = Error;
  fn try_into(self) -> Result<f64, Self::Error> {
    match &self.token {
      Token::Uint(i) => return i.to_string().parse::<f64>().map_err(ErrorKind::from).when("try_into_f64"),
      Token::Int(i) => return I256::from_raw(i.clone()).to_string().parse::<f64>().map_err(ErrorKind::from).when("try_into_f64"),
      Token::FixedBytes(i) => {
        match &self.ty {
          Some(Type::Number(NumberSuffix::F(64))) => {
            let mut t = [0u8; 8];
            if i.len() != t.len() {
              return Err(ErrorKind::custom("fixed bytes len mismatch").when("try_into_f64"))
            }
            t.clone_from_slice(i);
            return Ok(f64::from_be_bytes(t))
          }
          Some(Type::Number(NumberSuffix::F(32))) => {
            let mut t = [0u8; 4];
            if i.len() != t.len() {
              return Err(ErrorKind::custom("fixed bytes len mismatch").when("try_into_f64"))
            }
            t.clone_from_slice(i);
            return Ok(f32::from_be_bytes(t) as _)
          }
          _ => {}
        }
      },
      _ => {}
    };
    return Err(ErrorKind::NotCompatible(format!("{}", self.abi)).when("try_into_f64"))
  }
}
