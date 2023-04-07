use std::{collections::BTreeMap, rc::Rc};

use crate::{typing::Type, abi::Scope};

pub fn globals() -> Scope {
  let mut abi = ethabi::Contract {
    constructor: None,
    functions: BTreeMap::new(),
    events: Default::default(),
    errors: Default::default(),
    receive: Default::default(),
    fallback: Default::default(),
  };
  abi.functions.insert("deploy".to_string(), vec![
    ethabi::Function {
      name: "deploy".to_string(),
      inputs: vec![ethabi::Param { name: "name".to_string(), kind: ethabi::ParamType::Bytes, internal_type: None }],
      outputs: vec![ethabi::Param { name: "".to_string(), kind: ethabi::ParamType::Address, internal_type: None }],
      constant: None,
      state_mutability: ethabi::StateMutability::Payable
    }]);
  let mut result = Scope::new("@Global", abi);
  result
}
