use std::str::FromStr;

use bigdecimal::{BigDecimal, FromPrimitive, num_bigint::BigInt};
use ethabi::Address;
use ethers::{signers::LocalWallet, types::TransactionReceipt};

use crate::{
  vm::{ValueKind, Value},
  ast::{TypedNumber, TypedString, StringPrefix, NumberSuffix}, typing::{Type, ModuleName},
};

use super::{conv::{try_convert_hex_to_bytes, ErrorExt, ErrorKind}, Error, value_into::Number};

impl Value {
  pub fn from_address(address: Address, name: Option<ModuleName>) -> Self {
    match name {
      Some(name) => Self { v: ValueKind::Address(address), ty: Type::Contract(name) },
      None => Self { v: ValueKind::Address(address), ty: Type::Address },
    }

  }
  pub fn from_bool(bool: bool) -> Self {
    Self { v: ValueKind::Bool(bool), ty: Type::Bool }
  }
  pub fn from_string(string: String) -> Self {
    Self { v: ValueKind::String(string), ty: Type::String }
  }
  pub fn from_bytes(bytes: Vec<u8>) -> Self {
    Self { v: ValueKind::Bytes(bytes), ty: Type::Bytes }
  }
  pub fn from_bytecode(bytes: Vec<u8>, name: Option<ModuleName>) -> Self {
    match name {
      Some(name) => Self { v: ValueKind::Bytecode(bytes), ty: Type::ContractType(name) },
      None => Self { v: ValueKind::Bytecode(bytes), ty: Type::Bytes },
    }
  }
  pub fn from_number(base: BigDecimal, suffix: NumberSuffix) -> Self {
    Self { v: ValueKind::Number(base), ty: Type::Number(suffix) }
  }
  pub fn from_wallet(wallet: LocalWallet) -> Self {
    Self { v: ValueKind::Wallet(wallet), ty: Type::Wallet }
  }
  pub fn from_receipt(receipt: TransactionReceipt) -> Self {
    Self { v: ValueKind::Receipt(receipt), ty: Type::Receipt }
  }
  pub fn from_array(array: Vec<ValueKind>, item_ty: Type) -> Self {
    let len = array.len();
    Self { v: ValueKind::Array(array, item_ty.clone()), ty: Type::FixedArray(Box::new(item_ty), len) }
  }
  pub fn from_tuple(array: Vec<Value>) -> Self {
    todo!()
    // Self { v: ValueKind::Tuple(array), ty: todo!() }
  }
}

impl TryFrom<Number> for Value {
  type Error = Error;
  fn try_from(value: Number) -> Result<Self, Self::Error> {
    let result = match value {
      Number::I(i) =>
        Value::from_number(BigDecimal::from_str(&i.to_string()).unwrap(), NumberSuffix::Signed),
      Number::U(i) =>
        Value::from_number(BigDecimal::from_str(&i.to_string()).unwrap(), NumberSuffix::None),
      Number::F(_) => {
        let f: f64 = value.try_into()?;
        let base = BigDecimal::from_f64(f).ok_or_else(|| ErrorKind::custom("convert f64 from Number in ValueKind")).context("from number")?;
        // ValueKind::Number(BigDecimal, ())
        Value::from_number(base, NumberSuffix::F(64))
      }
    };
    Ok(result)
  }
}

impl TryFrom<TypedNumber> for Value {
  type Error = Error;
  fn try_from(value: TypedNumber) -> Result<Self, Self::Error> {
    trace!("try_from(Value<=TypedNumber): {:?}", value.suffix);
    let base = bigdecimal::BigDecimal::from_str(&value.value).context("from typed_number")?;
    return Ok(Value::from_number(base, value.suffix));
  }
}

impl TryFrom<TypedString> for Value {
  type Error = Error;

  fn try_from(value: TypedString) -> std::result::Result<Self, Self::Error> {
    let bytes = match value.prefix {
      StringPrefix::None => {
        let string = String::from_utf8(value.value).context("try_from TypedString")?;
        return Ok(Value::from_string(string))
      },
      StringPrefix::Hex | StringPrefix::Key | StringPrefix::Bytecode => {
        // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
        try_convert_hex_to_bytes(value.value.as_slice()).context("try_from TypedString")?
      }
      StringPrefix::Address => {
        let addr = try_convert_hex_to_bytes(value.value.as_slice()).context("try_from TypedString")?;
        return Ok(Value::from_address(Address::from_slice(&addr), None))
      }
      StringPrefix::Byte => {
        value.value
      }
      StringPrefix::Contract => todo!(),
      // _ => return Err(ErrorKind::UnknownPrefix(value.prefix.to_string())).when("try_from"),
    };
    match value.prefix {
      StringPrefix::Key => {
        let wallet = LocalWallet::from_bytes(&bytes).context("try_from TypedString")?;
        return Ok(Value::from_wallet(wallet))
      }
      StringPrefix::Bytecode => {
        warn!("fixme: from bytecode");
        return Ok(Value::from_bytecode(bytes, None));
      }
      _ => {}
    }
    Ok(Value::from_bytes(bytes))
  }
}
