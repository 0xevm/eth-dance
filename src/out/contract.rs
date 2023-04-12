use std::collections::BTreeMap;

use ethabi::ethereum_types::H256;
use serde::{Serialize, Deserialize};

use crate::typing::Type;

use super::cache::{Item, Value};

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
    if let Some(Value::Address(addr)) = &v.value {
      let mut item = ContractItem { address: addr.to_string(), contract_path: None, bytecode_hash: None };
      if let Type::Contract(contract_name) = &v.ty {
        item.bytecode_hash = items.get(contract_name).map(|i| i.value_hash);
        item.contract_path = Some(contract_name.to_string());
      }
      result.insert(n.to_string(), item);
    }
  }
  result
}
