use std::{collections::BTreeMap, rc::Rc};

use crate::typing::Type;

pub type Func = Rc<FuncImpl>;

#[derive(Debug, Default)]
pub struct FuncImpl {
  pub ns: String,
  pub name: String,
  pub funcs: Vec<Rc<ethabi::Function>>,
}
impl FuncImpl {
  fn new_unchecked() -> Self {
    Self::default()
  }

  pub fn infer_type(&self, args: &[Type]) -> Option<Type> {
    if self.ns == "@Global" && self.name == "contract" {
      info!("@Global.contract: {:?}", args.get(0));
      return Some(args.get(0).cloned().unwrap_or_default())
    }
    if let Some(func) = self.select(args) {
      warn!("fixme: match input");
      if func.outputs.is_empty() {
        return Some(Type::NoneType)
      } else if func.outputs.len() == 1 {
        return Some(Type::Abi(func.outputs.first().unwrap().kind.clone()))
      } else {
        let outputs = func.outputs.iter().map(|i| i.kind.clone()).collect::<Vec<_>>();
        return Some(Type::Abi(ethabi::ParamType::Tuple(outputs)))
      }
    }
    None
  }

  pub fn select(&self, args: &[Type]) -> Option<Rc<ethabi::Function>> {
    for func in &self.funcs {
      warn!("select {}.{} {} {}", self.ns, self.name, func.inputs.len(), args.len());
      if func.inputs.len() != args.len() {
        continue
      }
      warn!("fixme: match input");
      return Some(func.clone())
    }
    None
  }
}

pub fn globals() -> BTreeMap<String, Func> {
  let mut result = BTreeMap::new();
  for (name, mut func) in [
    ("contract", FuncImpl::new_unchecked()),
  ] {
    func.ns = "@Global".to_string();
    func.name = name.to_string();
    result.insert(name.to_string(), Rc::new(func));
  }
  result
}
