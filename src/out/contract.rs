use std::collections::BTreeMap;

use ethabi::ethereum_types::H256;
use ethers::utils::to_checksum;
use serde::{Serialize, Deserialize};

use crate::{typing::{Type, Modules}, vm::Value};

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

pub fn gen(items: &BTreeMap<String, Item>, modules: &Modules) -> BTreeMap<String, ContractItem> {
  let mut result = BTreeMap::new();
  for (n, v) in items {
    if let Some(addr) = &v.value.as_ref().and_then(Value::as_address) {
      let mut item = ContractItem { address: to_checksum(addr, None), contract_path: None, bytecode_hash: None };
      if let Some(Type::Contract(contract_name)) = &v.value.as_ref().map(|i| &i.ty) {
        item.bytecode_hash = modules.get(contract_name).and_then(|i| i.bytecode.as_ref()).map(|bytes| ethers::utils::keccak256(bytes.as_bytes()).into()); // TODO hex decode first
        item.contract_path = Some(modules.get(contract_name).map(|i| i.name.clone()).unwrap_or_else(|| contract_name.to_string()));
      }
      result.insert(n.to_string(), item);
    }
  }
  result
}
