use std::collections::BTreeMap;

use ethers::types::H256;
use serde::{Serialize, Deserialize};

use crate::{
  typing::{Type, Typing},
  vm::{VM, ValueKind},
};

#[serde_with::serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Item {
  pub id: (u64, u64),
  pub name: Option<String>,
  #[serde_as(as = "Option<serde_with::DisplayFromStr>")]
  #[serde(skip_serializing_if = "Option::is_none")]
  pub value: Option<ValueKind>,
  pub value_hash: H256,
  #[serde_as(as = "serde_with::DisplayFromStr")]
  pub ty: Type,
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
    let name = match typing.get_info_view(*id).display.clone() {
      s if s.starts_with("$$") => None,
      s => Some(s),
    };
    let ty = typing.get_info_view(*id).ty().clone();
    let v = match ty {
      Type::ContractType(_) => None,
      _ => Some(value.clone()),
    };
    let id = (id.0, id.1);
    let mut item = Item {
      id, name: name.clone(), ty,
      value: v,
      value_hash: ethers::utils::keccak256(value.value_str().as_bytes()).into(),
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
