use std::collections::BTreeMap;

use crate::typing::{Typing, ExprT, Id};

pub struct Error {

}
pub type Result<T, E=Error> = std::result::Result<T, E>;

pub struct Value {
  pub value: ethabi::Token,
  pub ty: ethabi::ParamType,
}

pub struct VM {
  pub values: BTreeMap<Id, Value>,
}

pub fn run_plan(typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    match &info.expr.t {
      ExprT::Func { func, this, args, send } => {
        if func.ns == "@Global" && func.name == "contract" {
        } else {

        }
      }
      _ => unimplemented!()
    }
  }
  Ok(())
}
