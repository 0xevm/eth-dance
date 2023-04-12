pub mod serde;
pub mod str;
pub mod value_from;
pub mod value_into;
pub mod conv;

pub use conv::Error;
use ethabi::{ParamType, Token, Address};
use ethers::{
  signers::{LocalWallet, Signer},
  types::I256,
};

use crate::{typing::Type, vm::Value};

use self::conv::{try_convert_u256_to_h256, try_trim_u256, try_trim_i256};

pub fn try_convert(ty: &Type, mut value: Value) -> Result<Value, Error> {
  if Some(ty) == value.ty.as_ref() {
    return Ok(value)
  }
  if let Some(abi) = ty.abi() {
    if abi == value.abi {
      value.ty = Some(ty.clone());
      return Ok(value);
    }
  }
  let mut value = match (ty, &value.abi) {
    // (Type::ContractType(_), ParamType::Bytes) |
    // (Type::Contract(_), ParamType::Address) |
    // (Type::Number(_), ParamType::Int(_)) |
    // (Type::Number(_), ParamType::Uint(_)) |
    // (Type::String(_), ParamType::Bytes)
    //   => {
    //     value
    //   },
    (Type::String(s), ParamType::Bytes) if s == "key"
      => {
        let address = match &value.token {
          Token::Bytes(bytes) => LocalWallet::from_bytes(bytes).unwrap().address(),
          _ => unreachable!(),
        };
        Value { token: Token::Address(address), abi: ParamType::Address, ty: None }
      },
    (Type::Contract(_), ParamType::Uint(256))
      => {
        let new_value: Address = match value.token {
          Token::Uint(i) | Token::Int(i) =>
            try_convert_u256_to_h256(i).into(),
          _ => unreachable!(),
        };
        value.token = Token::Address(new_value);
        value.abi = ParamType::Address;
        value
      }
    (Type::NoneType, _) => {
      value.token = Token::FixedBytes(vec![]);
      value.abi = ParamType::FixedBytes(0);
      value
    }
    // (Type::Abi(x), y) if x == y => value,
    (Type::Abi(ParamType::Uint(s)), ParamType::Int(_)) |
    (Type::Abi(ParamType::Uint(s)), ParamType::Uint(_)) => {
      let token = match value.token {
        Token::Uint(i) => try_trim_u256(i, *s)?,
        Token::Int(i) => try_trim_u256(i, s.saturating_sub(1))?,
        _ => unreachable!(),
      };
      value.token = Token::Uint(token);
      value.abi = ParamType::Uint(*s);
      value
    }
    (Type::Abi(ParamType::Int(s)), ParamType::Int(_)) |
    (Type::Abi(ParamType::Int(s)), ParamType::Uint(_)) => {
      let token = match value.token {
        Token::Int(i) => try_trim_i256(I256::from_raw(i), *s)?.into_raw(),
        Token::Uint(i) => try_trim_u256(i, s.saturating_sub(1))?,
        _ => unreachable!(),
      };
      value.token = Token::Int(token);
      value.abi = ParamType::Uint(*s);
      value
    }
    _ => {
      warn!("fixme: convert to ty: {:?} => {:?}: {}", value.abi, ty, value.token);
      value
    }
  };
  value.ty = Some(ty.clone());
  Ok(value)
}
