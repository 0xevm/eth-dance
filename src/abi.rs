use std::{collections::BTreeMap, rc::Rc};

pub use anyhow::Result;
pub use ethabi::Contract as ContractAbi;
pub use ethabi::Function as FunctionAbi;
use ethabi::{ParamType};

use crate::typing::Type;

#[derive(Debug)]
pub struct Scope {
  pub name: String,
  pub abi: Option<ContractAbi>,
  pub funcs: BTreeMap<String, Vec<Func>>,
}

pub type Func = Rc<FuncImpl>;
#[derive(Debug)]
pub struct FuncImpl {
  pub ns: String,
  pub name: String,
  pub abi: Option<FunctionAbi>,
  pub signature: String,
  pub selector: [u8; 4],
  pub input_types: Vec<ParamType>,
  pub output_types: Vec<ParamType>,
}

impl Scope {
  pub fn new(name: &str, abi: ContractAbi) -> Self {
    let mut funcs: BTreeMap<String, Vec<_>> = BTreeMap::new();
    for (n, v) in &abi.functions {
      for f in v {
        funcs.entry(n.to_string()).or_default().push(Rc::new(FuncImpl {
          ns: name.to_string(),
          name: f.name.clone(),
          abi: Some(f.clone()),
          signature: f.signature(),
          selector: f.short_signature(),
          input_types: f.inputs.iter().map(|i| i.kind.clone()).collect(),
          output_types: f.outputs.iter().map(|i| i.kind.clone()).collect(),
        }))
      }
    }
    Self { name: name.to_string(), abi: Some(abi), funcs }
  }

  pub fn select(&self, name: &str, args: &[Type]) -> Option<Func> {
    if let Some(v) = self.funcs.get(name) {
      for f in v {
        if f.input_types.len() != args.len() {
          continue;
        }
        return Some(f.clone())
      }
    }
    None
  }
}

impl FuncImpl {
  pub fn ty(&self) -> Option<Type> {
    if self.output_types.is_empty() {
      return Some(Type::NoneType)
    } else if self.output_types.len() == 1 {
      return Some(Type::Abi(self.output_types.first().unwrap().clone()))
    } else {
      let outputs = self.output_types.iter().map(|i| i.clone()).collect::<Vec<_>>();
      return Some(Type::Abi(ethabi::ParamType::Tuple(outputs)))
    }
  }
}

pub fn load_abi(name: &str, input: &str) -> Result<Scope> {
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
  let abi = ContractAbi::load(io)?;
  Ok(Scope::new(name, abi))
}

pub fn globals() -> Scope {
  let mut abi = ContractAbi {
    constructor: None,
    functions: BTreeMap::new(),
    events: Default::default(),
    errors: Default::default(),
    receive: Default::default(),
    fallback: Default::default(),
  };
  abi.functions.insert("deploy".to_string(), vec![
    FunctionAbi {
      name: "deploy".to_string(),
      inputs: vec![ethabi::Param { name: "name".to_string(), kind: ethabi::ParamType::Bytes, internal_type: None }],
      outputs: vec![ethabi::Param { name: "".to_string(), kind: ethabi::ParamType::Address, internal_type: None }],
      constant: None,
      state_mutability: ethabi::StateMutability::Payable
    }]);
  Scope::new("@Global", abi)
}
