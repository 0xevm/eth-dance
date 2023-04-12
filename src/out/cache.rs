use std::collections::BTreeMap;

use ethers::{core::utils::to_checksum, types::{I256, H256}};
use ethabi::{
  Token, ParamType,
  token::{LenientTokenizer, Tokenizer},
};
use serde::{Serialize, Deserialize};

use crate::{
  convert::serde as serde_impl,
  typing::{Type, Typing},
  vm::VM,
};

#[serde_with::serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Value {
  Value(Vec<Value>),
  Bytes(#[serde_as(as = "serde_impl::Token")] (Token, ParamType)),
  Address(String),
  Number(String),
  Bool(bool),
  String(String),
}

impl From<(Token, ParamType)> for Value {
  fn from((token, abi): (Token, ParamType)) -> Self {
    match token {
      Token::Address(v) => Value::Address(to_checksum(&v, None)),
      Token::Int(v) => Value::Number(I256::from_raw(v).to_string()),
      Token::Uint(v) => Value::Number(v.to_string()),
      Token::Bool(b) => Value::Bool(b),
      Token::String(s) => Value::String(s),
      Token::FixedBytes(_) | Token::Bytes(_) => Value::Bytes((token, abi)),
      Token::FixedArray(v) | Token::Array(v)
        => {
          let t = match abi {
            ParamType::FixedArray(i, _) | ParamType::Array(i) => *i,
            _ => unreachable!(),
          };
          Value::Value(v.into_iter().map(|v| Value::from((v, t.clone()))).collect())
        }
      Token::Tuple(v) => {
        let t = match abi {
          ParamType::Tuple(i) => i,
          _ => unreachable!(),
        };
        Value::Value(v.into_iter().zip(t).map(|v| Value::from(v)).collect())

      }
    }
  }
}

impl TryInto<(Token, ParamType)> for Value {
  type Error = &'static str;
  fn try_into(self) -> Result<(Token, ParamType), Self::Error> {
    let result = match self {
      Value::Value(_) => todo!(),
      Value::Bytes(_) => todo!(),
      Value::Address(_) => todo!(),
      Value::Number(v) => {
        if v.starts_with("-") {
          let i = LenientTokenizer::tokenize_int(v.as_str()).map_err(|_| "parse int")?;
          (Token::Int(i.into()), ParamType::Int(256))
        } else {
          let i = LenientTokenizer::tokenize_uint(v.as_str()).map_err(|_| "parse int")?;
          (Token::Uint(i.into()), ParamType::Uint(256))
        }
      }
      Value::Bool(v) => (Token::Bool(v), ParamType::Bool),
      Value::String(v) => (Token::String(v), ParamType::String),
    };
    Ok(result)
  }
}

#[serde_with::serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Item {
  pub id: u64,
  pub name: Option<String>,
  #[serde(flatten)]
  pub value: Option<Value>,
  pub value_hash: H256,
  #[serde_as(as = "serde_with::DisplayFromStr")]
  pub ty: Type,
  // pub code: ExprCode,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Output {
  pub vars: BTreeMap<String, Item>,
  pub ids: BTreeMap<u64, Item>,
}

pub fn from_vm(vm: &VM, typing: &Typing) -> Output {
  let mut out = Output::default();
  for (id, value) in &vm.values {
    let name = match typing.get_info_view(*id).display.clone() {
      s if s.starts_with("$$") => None,
      s => Some(s),
    };
    let ty = typing.get_info_view(*id).ty().clone();
    let v = match ty {
      Type::ContractType(_) => None,
      _ => Some((value.token.clone(), value.abi.clone()).into()),
    };
    let id = id.0;
    let mut item = Item {
      id, name: name.clone(), ty,
      value: v,
      value_hash: ethers::utils::keccak256(ethabi::encode(&[value.token.clone()])).into(),
    };
    if let Some(name) = name {
      out.vars.insert(name, item.clone());
      item.value = None;
    }
    out.ids.insert(id, item);
  }
  out
}
