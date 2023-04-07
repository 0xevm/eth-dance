use std::{collections::BTreeMap, rc::Rc};

pub use anyhow::Result;
use ethabi::Contract;

use crate::global::{Func, FuncImpl};

pub fn load_abi(input: &str) -> Result<Contract> {
  let mut abi_input = String::new();
  let compiled = serde_json::from_str::<serde_json::Value>(input)?;
  if let Some(map) = compiled.as_object() {
    if map.contains_key("abi") {
      let abi = map.get("abi").unwrap();
      abi_input = serde_json::to_string(abi)?;
    }
  }
  let input = if abi_input.is_empty() {
    input
  } else { &abi_input };

  let io = std::io::Cursor::new(input);
  let contract = Contract::load(io)?;
  Ok(contract)
}

pub fn contract_to_scope(ns: &str, contract: &Contract) -> BTreeMap<String, Func> {
  let mut result = BTreeMap::new();
  for (name, funcs) in &contract.functions {
    let func = Rc::new(FuncImpl { ns: ns.to_string(), name: name.to_string(), funcs: funcs.iter().map(|i| Rc::new(i.clone())).collect() });
    result.insert(name.to_string(), func);
  }
  result
}
