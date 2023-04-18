use std::{string::FromUtf8Error, num::ParseFloatError};

use ethers::{types::{I256, U256, H256}, signers::WalletError};

#[derive(Debug, thiserror::Error)]
pub enum ErrorKind {
  #[error("connot convert from {0}")]
  NotCompatible(String),
  #[error("load utf8 {0}")]
  FromUtf8(#[from] FromUtf8Error),
  #[error("parse float {0}")]
  ParseFloat(#[from] ParseFloatError),
  #[error("trim uint to {0}")]
  OutOfBounds(usize),
  #[error("unknown prefix {0}")]
  UnknownPrefix(String),
  #[error("custom error {0}")]
  Custom(String),
  #[error("wallet {0}")]
  Wallet(#[from] WalletError),
  #[error("wallet {0}")]
  Number(&'static str),
}

#[derive(Debug, thiserror::Error)]
#[error("convert {dst}")]
pub struct Error {
  #[source]
  pub kind: ErrorKind,
  pub dst: &'static str,
}

impl ErrorKind {
  pub fn custom<S: ToString>(s: S) -> Self {
    ErrorKind::Custom(s.to_string())
  }
  pub fn custom_error<E: std::error::Error>(s: E) -> Self {
    ErrorKind::Custom(format!("{:?}", s))
  }
  pub fn when(self, dst: &'static str) -> Error {
    Error { kind: self, dst }
  }
}

pub trait ErrorKindExt<T> {
  fn when(self, s: &'static str) -> Result<T, Error>;
}
impl<T> ErrorKindExt<T> for Result<T, ErrorKind> {
  fn when(self, dst: &'static str) -> Result<T, Error> {
    self.map_err(|kind| kind.when(dst))
  }
}

pub fn try_convert_hex_to_bytes(mut input: &[u8]) -> Result<Vec<u8>, Error> {
  // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
  if input.starts_with("0x".as_bytes()) {
    input = &input[2..];
  }
  let result = hex::decode(input).map_err(ErrorKind::custom_error).when("hex_to_bytes")?;
  Ok(result)
}

pub fn try_convert_u256_to_h256(i: U256) -> H256 {
  let mut bytes = [0u8; 32];
  i.to_big_endian(&mut bytes);
  H256::from(bytes)
}

pub fn try_trim_u256(i: U256, n: usize) -> Result<U256, Error> {
  if i >= U256::from(2).pow(U256::from(n)) {
    return Err(ErrorKind::OutOfBounds(n)).when("trim_u256")
  }
  Ok(i)
}

pub fn try_trim_i256(i: I256, n: usize) -> Result<I256, Error> {
  if i >= I256::from(2).pow(n as _) {
    return Err(ErrorKind::OutOfBounds(n)).when("trim_i256")
  }
  if i < -I256::from(2).pow(n as _) {
    return Err(ErrorKind::OutOfBounds(n)).when("trim_i256")
  }
  Ok(i)
}
