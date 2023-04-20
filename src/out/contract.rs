use std::collections::BTreeMap;

use ethabi::ethereum_types::H256;
use serde::{Serialize, Deserialize};

use crate::{typing::Type, vm::Value};

use super::cache::Item;

#[derive(Debug, Serialize, Deserialize)]
pub struct ContractItem {
  pub address: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub contract_path: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub bytecode_hash: Option<H256>,
  // TODO: add tx_hash, time
}

pub fn gen(items: &BTreeMap<String, Item>) -> BTreeMap<String, ContractItem> {
  let mut result = BTreeMap::new();
  for (n, v) in items {
    if let Some(addr) = &v.value.as_ref().and_then(Value::as_address) {
      let mut item = ContractItem { address: addr.to_string(), contract_path: None, bytecode_hash: None };
      if let Some(Type::Contract(contract_name)) = &v.value.as_ref().map(|i| &i.ty) {
        item.bytecode_hash = items.get(contract_name).map(|i| i.value_hash);
        item.contract_path = Some(contract_name.to_string());
      }
      result.insert(n.to_string(), item);
    }
  }
  result
}
