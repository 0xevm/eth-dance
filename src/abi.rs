use std::{collections::BTreeMap, rc::Rc};

pub use anyhow::Result;
pub use ethabi::Contract as ContractAbi;
pub use ethabi::Function as FunctionAbi;
pub use ethabi::Constructor as ConstructorAbi;
use ethabi::ParamType;
use ethabi::StateMutability;

use crate::typing::Type;

#[derive(Debug)]
pub struct Module {
  pub name: String,
  pub abi: Option<ContractAbi>,
  pub bytecode: Option<String>,
  pub funcs: BTreeMap<String, Vec<Func>>,
}

pub type Func = Rc<FuncImpl>;
#[derive(Debug, Default)]
pub struct FuncImpl {
  pub ns: String,
  pub name: String,
  pub is_send: bool,
  pub abi: Option<FunctionAbi>,
  pub signature: String,
  pub selector: [u8; 4],
  pub input_types: Vec<ParamType>,
  pub output_types: Vec<ParamType>,
}

impl Module {
  pub fn new(name: &str, abi: ContractAbi, bytecode: Option<String>) -> Self {
    let mut funcs: BTreeMap<String, Vec<_>> = BTreeMap::new();
    for (n, v) in &abi.functions {
      for f in v {
        funcs.entry(n.to_string()).or_default().push(Rc::new(FuncImpl {
          ns: name.to_string(),
          name: f.name.clone(),
          is_send: f.state_mutability != StateMutability::Pure && f.state_mutability != StateMutability::View,
          abi: Some(f.clone()),
          signature: f.signature(),
          selector: f.short_signature(),
          input_types: f.inputs.iter().map(|i| i.kind.clone()).collect(),
          output_types: f.outputs.iter().map(|i| i.kind.clone()).collect(),
        }))
      }
    }
    let ctor_inputs = if let Some(ConstructorAbi { inputs }) = &abi.constructor {
      inputs.clone()
    } else {
      vec![]
    };
    funcs.entry("constructor".to_string()).or_default().push(Rc::new(FuncImpl {
      ns: name.to_string(),
      name: "constructor".to_string(),
      is_send: true,
      abi: None,
      signature: String::new(),
      selector: Default::default(),
      input_types: ctor_inputs.iter().map(|i| i.kind.clone()).collect(),
      output_types: vec![ParamType::Address],
    }));
    Self { name: name.to_string(), abi: Some(abi), bytecode, funcs }
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
  pub fn returns(&self) -> Type {
    if self.output_types.is_empty() {
      Type::NoneType
    } else if self.output_types.len() == 1 {
      Type::Abi(self.output_types.first().unwrap().clone())
    } else {
      let outputs = self.output_types.iter().map(|i| i.clone()).collect::<Vec<_>>();
      Type::Abi(ethabi::ParamType::Tuple(outputs))
    }
  }
}

pub fn load_abi(name: &str, input: &str) -> Result<Module> {
  let mut abi_input = String::new();
  let mut bytecode = None;
  let compiled = serde_json::from_str::<serde_json::Value>(input)?;
  if let Some(map) = compiled.as_object() {
    if map.contains_key("abi") {
      let abi = map.get("abi").unwrap();
      abi_input = serde_json::to_string(abi)?;
    }
    if let Some(bytecode_obj) = map.get("bytecode") {
      bytecode = bytecode_obj.as_str().map(|i| i.to_string());
      if bytecode.is_none() {
        bytecode = bytecode_obj.as_object().and_then(|i| i.get("object")).and_then(|i| i.as_str()).map(|i| i.to_string());
      }
    }
  }
  let input = if abi_input.is_empty() {
    input
  } else { &abi_input };

  let io = std::io::Cursor::new(input);
  let abi = ContractAbi::load(io)?;
  Ok(Module::new(name, abi, bytecode))
}

pub fn global_module(module_name: &'static str, funcs: &[(&str, Vec<ParamType>, Vec<ParamType>)]) -> Module {
  let mut module = Module { name: module_name.to_string(), abi: None, bytecode: None, funcs: BTreeMap::new() };
  for (n, input, output) in funcs {
    module.funcs.entry(n.to_string()).or_default().push(Func::new(
      FuncImpl {
        ns: module_name.to_string(), name: n.to_string(),
        is_send: false,
        abi: None, signature: Default::default(), selector: Default::default(),
        input_types: input.clone(), output_types: output.clone(),
      }));
  }
  module
}

pub fn globals() -> Vec<Module> {
  vec![
    global_module("@Global", &[
      ("deploy", vec![], vec![ParamType::Address]),
    ]),

    global_module("@assert", &[
      ("eq", vec![ParamType::Bytes, ParamType::Bytes], vec![]),
    ]),
  ]
}
