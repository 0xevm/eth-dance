use std::{string::FromUtf8Error, num::ParseFloatError};

use ethers::types::{I256, U256, H256};

use crate::vm::Value;

#[derive(Debug, thiserror::Error)]
pub enum ErrorKind {
  #[error("connot convert from {0}")]
  NotCompatible(String),
  #[error("trim to {0} bits out of bounds")]
  OutOfBounds(usize),
  #[error("unknown prefix {0}")]
  UnknownPrefix(String),
  #[error("number {0}")]
  Number(&'static str),
  #[error("custom: {0}")]
  Custom(String),

  #[error(transparent)]
  FromUtf8(#[from] FromUtf8Error),
  #[error(transparent)]
  ParseFloat(#[from] ParseFloatError),

  #[error(transparent)]
  Wallet(#[from] ethers::signers::WalletError),
  #[error(transparent)]
  BigDecimal(#[from] bigdecimal::ParseBigDecimalError),
  #[error(transparent)]
  U256(#[from] ethabi::ethereum_types::FromDecStrErr),
  #[error(transparent)]
  I256(#[from] ethers::types::ParseI256Error),
}

#[derive(Debug, thiserror::Error)]
#[error("convert {dst}")]
pub struct Error {
  #[source]
  pub kind: ErrorKind,
  pub dst: String,
}

impl ErrorKind {
  pub fn custom<S: ToString>(s: S) -> Self {
    ErrorKind::Custom(s.to_string())
  }
  pub fn custom_error<E: std::error::Error>(s: E) -> Self {
    ErrorKind::Custom(format!("{:?}", s))
  }
  pub fn context<S: ToString>(self, dst: S) -> Error {
    Error { kind: self, dst: dst.to_string() }
  }
  pub fn when(self, s: &'static str, v: &Value) -> Error {
    Error { kind: self, dst: format!("when convert {} from {}", s, v.ty)}
  }
}

pub type Result<T, E=Error> = std::result::Result<T, E>;

pub trait ErrorExt<T> {
  fn context<S: ToString>(self, s: S) -> Result<T, Error>;
  fn when(self, msg: &'static str, v: &Value) -> Result<T, Error>;
}
impl<T, E: Into<ErrorKind>> ErrorExt<T> for Result<T, E> {
  fn context<S: ToString>(self, dst: S) -> Result<T, Error> {
    self.map_err(|kind| kind.into().context(dst))
  }
  fn when(self, msg: &'static str, v: &Value) -> Result<T, Error> {
    self.map_err(|kind| kind.into().when(msg, v))
  }
}

pub fn try_convert_hex_to_bytes(mut input: &[u8]) -> Result<Vec<u8>, Error> {
  // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
  if input.starts_with("0x".as_bytes()) {
    input = &input[2..];
  }
  let result = hex::decode(input).map_err(ErrorKind::custom_error).context("hex_to_bytes")?;
  Ok(result)
}

pub fn try_convert_u256_to_h256(i: U256) -> H256 {
  let mut bytes = [0u8; 32];
  i.to_big_endian(&mut bytes);
  H256::from(bytes)
}

pub fn try_trim_u256(i: U256, n: usize) -> Result<U256> {
  if n == 256 { return Ok(i) }
  if i >= U256::from(2).pow(U256::from(n)) {
    return Err(ErrorKind::OutOfBounds(n)).context("trim_u256")
  }
  Ok(i)
}

pub fn try_trim_i256(i: I256, n: usize) -> Result<I256> {
  if n == 256 { return Ok(i) }
  if i >= I256::from(2).pow(n as _) {
    return Err(ErrorKind::OutOfBounds(n)).context("trim_i256")
  }
  if i < -I256::from(2).pow(n as _) {
    return Err(ErrorKind::OutOfBounds(n)).context("trim_i256")
  }
  Ok(i)
}
