use std::{collections::BTreeMap, rc::Rc};

use crate::typing::Type;

pub type Func = Rc<FuncImpl>;

#[derive(Debug, Default)]
pub struct FuncImpl {
  pub ns: String,
  pub name: String,
}
impl FuncImpl {
  fn new_unchecked() -> Self {
    Self::default()
  }

  pub fn infer_type(&self, args: Vec<Type>) -> Type {
    if self.ns == "@Global" && self.name == "contract" {
      info!("@Global.contract: {:?}", args.get(0));
      return args.get(0).cloned().unwrap_or_default()
    }
    warn!("fixme: infer_type");
    Type::None
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
