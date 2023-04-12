use ethabi::param_type::{ParamType as RemoteParamType, Writer, Reader};
use ethabi::token::{Token as RemoteToken, StrictTokenizer, Tokenizer};
use serde::{Serializer, Deserializer};
use serde_with::{SerializeAs, DeserializeAs};

pub struct ParamType;

impl SerializeAs<RemoteParamType> for ParamType {
  fn serialize_as<S: Serializer>(value: &RemoteParamType, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(Writer::write_for_abi(value, true).as_str())
  }
}

impl<'de> DeserializeAs<'de, RemoteParamType> for ParamType {
  fn deserialize_as<D: Deserializer<'de>>(deserializer: D) -> Result<RemoteParamType, D::Error> {
    let s: String = serde::Deserialize::deserialize(deserializer)?;
    Reader::read(&s).map_err(|e| serde::de::Error::custom(e))
  }
}

pub struct Token;

impl SerializeAs<(RemoteToken, RemoteParamType)> for Token {
  fn serialize_as<S: Serializer>(value: &(RemoteToken, RemoteParamType), serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(format!("{}: {}", value.1, value.0).as_str())
  }
}

impl<'de> DeserializeAs<'de, (RemoteToken, RemoteParamType)> for Token {
  fn deserialize_as<D: Deserializer<'de>>(deserializer: D) -> Result<(RemoteToken, RemoteParamType), D::Error> {
    let s: String = serde::Deserialize::deserialize(deserializer)?;
    if !s.contains(":") {
      return Err(serde::de::Error::custom("str does not contains \":\""));
    }
    let mut sp = s.splitn(2, ":");
    let ty = Reader::read(sp.next().unwrap()).map_err(serde::de::Error::custom)?;
    let v = StrictTokenizer::tokenize(&ty, &sp.next().unwrap()).map_err(serde::de::Error::custom)?;
    Ok((v, ty))
  }
}
