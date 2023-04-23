use std::collections::BTreeMap;

use ethabi::ethereum_types::H256;
use ethers::utils::to_checksum;
use serde::{Serialize, Deserialize};

use crate::{typing::{Type, Modules}, vm::{Value, ValueKind}};

use super::cache::Item;

#[derive(Debug, Serialize, Deserialize)]
pub struct ContractItem {
  pub address: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub contract_path: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub bytecode_hash: Option<H256>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub transaction_hash: Option<H256>,
  // TODO: add tx_hash, time
}

pub fn gen(items: &BTreeMap<String, Item>, modules: &Modules) -> BTreeMap<String, ContractItem> {
  let mut result = BTreeMap::new();
  for (n, v) in items {
    if let Some(addr) = &v.value.as_ref().and_then(Value::as_address) {
      let mut item = ContractItem { address: to_checksum(addr, None), contract_path: None, bytecode_hash: None, transaction_hash: None };
      match &v.value.as_ref().map(|i| &i.ty) {
        Some(Type::Contract(contract_name)) | Some(Type::ContractReceipt(contract_name)) => {
          let module = modules.get(&contract_name.0);
          item.bytecode_hash = module.and_then(|i| i.bytecode.as_ref()).map(|bytes| ethers::utils::keccak256(bytes.as_bytes()).into()); // TODO hex decode first
          item.contract_path = Some(module.map(|i| i.name.clone()).unwrap_or_else(|| contract_name.clone()).to_string());
        },
        _ => {}
      }
      if let Some(ValueKind::Receipt(receipt)) = &v.value.as_ref().map(|i| &i.v) {
        item.transaction_hash = Some(receipt.transaction_hash)
      }
      result.insert(n.to_string(), item);
    }
  }
  result
}
