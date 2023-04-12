use std::string::FromUtf8Error;

use ethabi::ethereum_types::{U256, H256};

#[derive(Debug, thiserror::Error)]
pub enum Error {
  #[error("connot convert from {src} to {dst}")]
  NotCompatible { src: String, dst: String },
  #[error("load utf8 {0}")]
  FromUtf8(#[from] FromUtf8Error),
  #[error("unknown prefix {0}")]
  UnknownPrefix(String),
  #[error("custom error {0}")]
  Custom(String),
}

impl Error {
  pub fn custom<S: ToString>(s: S) -> Self {
    Error::Custom(s.to_string())
  }
  pub fn custom_error<E: std::error::Error>(s: E) -> Self {
    Error::Custom(format!("{:?}", s))
  }
}

pub fn try_convert_hex_to_bytes(mut input: &[u8]) -> Result<Vec<u8>, Error> {
  // let str = String::from_utf8(value.value).map_err(|_| "utf8")?;
  if input.starts_with("0x".as_bytes()) {
    input = &input[2..];
  }
  let result = hex::decode(input).map_err(Error::custom_error)?;
  Ok(result)
}

pub fn try_convert_u256_to_h256(i: U256) -> H256 {
  let mut bytes = [0u8; 32];
  i.to_big_endian(&mut bytes);
  H256::from(bytes)
}
