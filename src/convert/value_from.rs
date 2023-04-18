use std::str::FromStr;

use ethabi::Address;
use ethers::signers::LocalWallet;

use crate::{
  vm::ValueKind,
  ast::{TypedNumber, TypedString, StringPrefix},
  typing::Type,
};

use super::{conv::{try_convert_hex_to_bytes, ErrorKindExt, ErrorKind}, Error};

impl From<Address> for ValueKind {
  fn from(value: Address) -> Self {
    ValueKind::Address(value, None)
  }
}

impl TryFrom<TypedNumber> for ValueKind {
  type Error = &'static str;
  fn try_from(value: TypedNumber) -> Result<Self, Self::Error> {
    trace!("try_from(Value<=TypedNumber): {:?}", value.suffix);
    let mut base = bigdecimal::BigDecimal::from_str(&value.value).map_err(|_| "convert to BigDecimal failed")?;
    return Ok(ValueKind::Number(base, value.suffix));
  }
}

impl TryFrom<TypedString> for ValueKind {
  type Error = Error;

  fn try_from(value: TypedString) -> std::result::Result<Self, Self::Error> {
    let ty = Some(Type::String(value.prefix.clone()));

    let bytes = match value.prefix {
      StringPrefix::None => {
        let string = String::from_utf8(value.value).map_err(ErrorKind::from).when("try_from")?;
        return Ok(ValueKind::String(string))
      },
      StringPrefix::Hex | StringPrefix::Key => {
        // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
        try_convert_hex_to_bytes(value.value.as_slice())?
      }
      StringPrefix::Address => {
        let addr = try_convert_hex_to_bytes(value.value.as_slice())?;
        return Ok(ValueKind::Address(Address::from_slice(&addr), None))
      }
      StringPrefix::Byte => {
        value.value
      }
      StringPrefix::Contract => todo!(),
      // _ => return Err(ErrorKind::UnknownPrefix(value.prefix.to_string())).when("try_from"),
    };
    match value.prefix {
      StringPrefix::Key => {
        let wallet = LocalWallet::from_bytes(&bytes).map_err(ErrorKind::from).when("try_from")?;
        return Ok(ValueKind::Wallet(wallet))
      }
      _ => {}
    }
    Ok(ValueKind::Bytes(bytes))
  }
}
