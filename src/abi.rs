use std::{collections::BTreeMap, rc::Rc};

pub use anyhow::Result;
pub use ethabi::Contract as ContractAbi;
pub use ethabi::Function as FunctionAbi;
use ethabi::{ParamType, Token};

use crate::typing::Type;
use crate::vm::Value;

#[derive(Debug)]
pub struct Scope {
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
  pub abi: Option<FunctionAbi>,
  pub signature: String,
  pub selector: [u8; 4],
  pub input_types: Vec<ParamType>,
  pub output_types: Vec<ParamType>,
}

impl Scope {
  pub fn new(name: &str, abi: ContractAbi, bytecode: Option<String>) -> Self {
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

  pub fn to_output(&self, mut out: Vec<Token>) -> Value {
    if out.len() == 1 {
      Value {
        token: out.remove(0),
        abi: self.output_types[0].clone(),
        ty: None,
      }
    } else {
      Value {
        token: Token::Tuple(out),
        abi: ParamType::Tuple(self.output_types.clone()),
        ty: None,
      }
    }
  }
}

pub fn load_abi(name: &str, input: &str) -> Result<Scope> {
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
  Ok(Scope::new(name, abi, bytecode))
}

pub fn global_scope(scope_name: &'static str, funcs: &[(&str, Vec<ParamType>, Vec<ParamType>)]) -> Scope {
  let mut scope = Scope { name: scope_name.to_string(), abi: None, bytecode: None, funcs: BTreeMap::new() };
  for (n, input, output) in funcs {
    scope.funcs.entry(n.to_string()).or_default().push(Func::new(
      FuncImpl {
        ns: scope_name.to_string(), name: n.to_string(),
        abi: None, signature: Default::default(), selector: Default::default(),
        input_types: input.clone(), output_types: output.clone(),
      }));
  }
  scope
}

pub fn globals() -> Vec<Scope> {
  vec![
    global_scope("@Global", &[
      ("deploy", vec![], vec![ParamType::Address]),
    ]),

    global_scope("@assert", &[
      ("eq", vec![ParamType::Bytes, ParamType::Bytes], vec![]),
    ]),
  ]
}
