use std::collections::BTreeMap;

use ethers::types::H256;
use serde::{Serialize, Deserialize};

use crate::{
  typing::{Type, Typing},
  vm::{VM, Value, ValueKey, ValueId},
};

#[serde_with::serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Item {
  #[serde_as(as = "serde_with::DisplayFromStr")]
  pub id: ValueId,
  #[serde(default, skip_serializing_if = "String::is_empty")]
  pub name: String,
  #[serde_as(as = "Vec<serde_with::DisplayFromStr>")]
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub keys: Vec<ValueKey>,
  #[serde_as(as = "Option<serde_with::DisplayFromStr>")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub value: Option<Value>,
  pub value_hash: H256,
  // pub code: ExprCode,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Output {
  pub last_id: u64,
  pub vars: BTreeMap<String, Item>,
  pub ids: Vec<Option<Item>>,
}

pub fn from_vm(vm: &VM, typing: &Typing) -> Output {
  let mut out = Output::default();
  let mut ids_cache = BTreeMap::new();
  for (id, value) in &vm.values {
    let name = match typing.get_info_view(id.code()).display.clone() {
      s if s.starts_with("$$") || s.is_empty() => None,
      s => Some(s),
    };
    let ty = typing.get_info_view(id.code()).ty().clone();
    let v = match ty {
      Type::ContractType(_) => None,
      _ => Some(value.clone()),
    };
    let info = vm.infos.get(id).unwrap().clone();
    let keys = vm.get_keys(*id).unwrap();
    let mut item = Item {
      name: info.name.clone(), keys,
      id: *id, value: v,
      value_hash: ethers::utils::keccak256(value.v.repr_str().as_bytes()).into(),
    };
    if let Some(name) = name {
      out.vars.insert(name, item.clone());
      item.value = None;
    }
    ids_cache.insert(id, item);
    if id.0 > out.last_id {
      out.last_id = id.0;
    }
  }
  for (_id, item) in ids_cache {
    // while out.ids.len() + 1 < id as usize {
    //   out.ids.push(None)
    // }
    out.ids.push(Some(item))
  }
  out
}
