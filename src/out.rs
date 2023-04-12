use std::collections::BTreeMap;

use ethabi::{Token, ParamType, ethereum_types::H256};
use serde::{Serialize, Deserialize};

use crate::{
  serde_impl,
  typing::{Type, Typing},
  vm::VM,
};

#[serde_with::serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Item {
  pub id: u64,
  pub name: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  #[serde_as(as = "Option<serde_impl::Token>")]
  pub value: Option<(Token, ParamType)>,
  pub value_hash: H256,
  pub ty: Type,
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
      _ => Some((value.token.clone(), value.abi.clone())),
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
