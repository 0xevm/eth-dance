pub mod serde;
pub mod str;
pub mod value_from;
pub mod value_into;
pub mod conv;

pub use conv::Error;
use ethabi::{ParamType, Token};
use ethers::{
  signers::Signer,
  types::I256,
};

use crate::{typing::Type, vm::ValueKind};

use self::{
  conv::{try_trim_u256, try_trim_i256, ErrorKind},
  value_into::Number
};

// pub struct EvmValue {
//   token: Token,
//   abi: ParamType,
// }

impl ValueKind {
  pub fn into_token(&self, abi: &ParamType) -> Result<Token, Error> {
    let result = match (self, abi) {
      (ValueKind::Address(addr, _), ParamType::Address) => Token::Address(*addr),
      (ValueKind::Wallet(wallet), ParamType::Address) => Token::Address(wallet.address()),

      (_, ParamType::Uint(s)) => {
        let number: Number = self.try_into()?;
        let i = match number {
          Number::U(i) => try_trim_u256(i, *s)?,
          Number::I(i) => try_trim_u256(i.into_raw(), s.saturating_sub(1))?,
          _ => todo!()
        };
        Token::Uint(i)
      }
      (_, ParamType::Int(n)) => {
        let number: Number = self.try_into()?;
        let i = match number {
          Number::I(i) => try_trim_i256(i, *n)?.into_raw(),
          Number::U(i) => try_trim_u256(i, n.saturating_sub(1))?,
          _ => todo!()
        };
        Token::Int(i)
      }
      _ => todo!("convert {:?} to {}", self, abi)
    };
    Ok(result)
  }

  pub fn from_token(token: Token) -> Result<Self, Error> {
    let result = match token {
      Token::Address(addr) => ValueKind::Address(addr, None),
      Token::FixedBytes(i) | Token::Bytes(i)
        => ValueKind::Bytes(i),
      Token::Int(i) => Number::I(I256::from_raw(i)).try_into().map_err(|e| ErrorKind::Number(e).when("from_token"))?,
      Token::Uint(i) => Number::U(i).try_into().map_err(|e| ErrorKind::Number(e).when("from_token"))?,
      Token::Bool(i) => ValueKind::Bool(i),
      Token::String(i) => ValueKind::String(i),
      Token::FixedArray(i) | Token::Array(i) => {
        if i.len() == 0 {
          return Ok(ValueKind::Array(Vec::new(), Type::NoneType))
        }
        let mut v = Vec::new();
        let mut ty = None;
        for x in i {
          v.push(Self::from_token_ty(x, ty.as_ref())?);
          if ty.is_none() {
            ty = Some(v.last().unwrap().ty())
          }
        }
        ValueKind::Array(v, ty.unwrap_or_default())
      }
      Token::Tuple(i) => ValueKind::Tuple(i.into_iter().map(Self::from_token).collect::<Result<_,_>>()?),
    };
    Ok(result)
  }

  pub fn from_token_ty(token: Token, ty: Option<&Type>) -> Result<Self, Error> {
    if ty.is_none() {
      return Self::from_token(token)
    }
    let result = match (token, ty.unwrap()) {
      (token, Type::Abi(_)) => Self::from_token(token)?,
      (Token::Address(addr), Type::Contract(name)) => ValueKind::Address(addr, Some(name.to_string())),

      (token, _) => {
        todo!("from_token: {:?} {:?}", token, ty)
      }
    };
    Ok(result)
  }
}
// pub fn try_convert(ty: &Type, value: EvmValue) -> Result<EvmValue, Error> {
//   if Some(ty) == value.ty.as_ref() {
//     return Ok(value)
//   }
//   let mut value = match (ty, &value.ty) {
//     (Type::String(StringPrefix::Address), Some(Type::String(StringPrefix::Key))) |
//     (Type::Abi(ParamType::Address), Some(Type::String(StringPrefix::Key))) => {
//       let address = match &value.token {
//         Token::Bytes(bytes) => LocalWallet::from_bytes(bytes).unwrap().address(),
//         _ => unreachable!(),
//       };
//       EvmValue { token: Token::Address(address), abi: ParamType::Address, ty: None }
//     }
//     _ => value
//   };
//   if let Some(abi) = ty.abi() {
//     if abi == value.abi {
//       value.ty = Some(ty.clone());
//       return Ok(value);
//     }
//   }
//   let mut value = match (ty, &value.abi) {
//     // (Type::ContractType(_), ParamType::Bytes) |
//     // (Type::Contract(_), ParamType::Address) |
//     // (Type::Number(_), ParamType::Int(_)) |
//     // (Type::Number(_), ParamType::Uint(_)) |
//     // (Type::String(_), ParamType::Bytes)
//     //   => {
//     //     value
//     //   },
//     (Type::Contract(_), ParamType::Uint(256))
//       => {
//         let new_value: Address = match value.token {
//           Token::Uint(i) | Token::Int(i) =>
//             try_convert_u256_to_h256(i).into(),
//           _ => unreachable!(),
//         };
//         value.token = Token::Address(new_value);
//         value.abi = ParamType::Address;
//         value
//       }
//     (Type::NoneType, _) => {
//       value.token = Token::FixedBytes(vec![]);
//       value.abi = ParamType::FixedBytes(0);
//       value
//     }
//     // (Type::Abi(x), y) if x == y => value,
//     (Type::Abi(ParamType::Uint(s)), ParamType::Int(_)) |
//     (Type::Abi(ParamType::Uint(s)), ParamType::Uint(_)) => {
//       let token = match value.token {
//         Token::Uint(i) => try_trim_u256(i, *s)?,
//         Token::Int(i) => try_trim_u256(i, s.saturating_sub(1))?,
//         _ => unreachable!(),
//       };
//       value.token = Token::Uint(token);
//       value.abi = ParamType::Uint(*s);
//       value
//     }
//     (Type::Abi(ParamType::Int(s)), ParamType::Int(_)) |
//     (Type::Abi(ParamType::Int(s)), ParamType::Uint(_)) => {
//       let token = match value.token {
//         Token::Int(i) => try_trim_i256(I256::from_raw(i), *s)?.into_raw(),
//         Token::Uint(i) => try_trim_u256(i, s.saturating_sub(1))?,
//         _ => unreachable!(),
//       };
//       value.token = Token::Int(token);
//       value.abi = ParamType::Uint(*s);
//       value
//     }
//     _ => {
//       warn!("fixme: convert to ty: {:?} => {:?}: {}", value.abi, ty, value.token);
//       value
//     }
//   };
//   value.ty = Some(ty.clone());
//   Ok(value)
// }
