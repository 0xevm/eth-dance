pub mod serde;
pub mod str;
pub mod value;
pub mod conv;

pub use conv::Error;
use ethabi::{ParamType, Token, Address};
use ethers::signers::{LocalWallet, Signer};

use crate::{typing::Type, vm::Value};

use self::conv::try_convert_u256_to_h256;

pub fn try_convert(ty: &Type, mut value: Value) -> Result<Value, &'static str> {
  if Some(ty) == value.ty.as_ref() {
    return Ok(value)
  }
  let mut value = match (ty, &value.abi) {
    (Type::ContractType(_), ParamType::Bytes) |
    (Type::Contract(_), ParamType::Address) |
    (Type::Number(_), ParamType::Int(_)) |
    (Type::Number(_), ParamType::Uint(_)) |
    (Type::String(_), ParamType::Bytes)
      => {
        value
      },
    (Type::String(s), ParamType::Address) if s == "key"
      => {
        let address = match &value.token {
          Token::Bytes(bytes) => LocalWallet::from_bytes(bytes).unwrap().address(),
          _ => unreachable!(),
        };
        Value { token: Token::Address(address), abi: ParamType::Address, ty: None }
      },
    (Type::Contract(_), ParamType::Uint(_))
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
    (Type::Abi(x), y) if x == y => value,
    _ => {
      warn!("fixme: convert to ty: {:?} => {:?}: {}", value.abi, ty, value.token);
      value
    }
  };
  value.ty = Some(ty.clone());
  Ok(value)
}
