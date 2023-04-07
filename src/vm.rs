use std::{collections::BTreeMap};

use ethabi::{Address, ethereum_types::{H160, U256}};

use crate::typing::{Typing, ExprT, Id, Type};

// pub struct Error {

// }
// pub type Result<T, E=Error> = std::result::Result<T, E>;
pub use anyhow::Result;

#[derive(Debug, Clone)]
pub struct Value {
  pub value: ethabi::Token,
  pub ty: ethabi::ParamType,
}

impl From<Address> for Value {
  fn from(value: Address) -> Self {
    Self {
      value: ethabi::Token::Address(value),
      ty: ethabi::ParamType::Address,
    }
  }
}

pub struct VM {
  pub values: BTreeMap<Id, Value>,
}

impl VM {
  pub fn new() -> Self {
    Self {
      values: Default::default(),
    }
  }
  pub fn set_value(&mut self, id: Id, ty: Type, value: Value) {
    self.values.insert(id, value);
  }
}

pub fn execute(vm: &mut VM, typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    match &info.expr.t {
      ExprT::None => {
        warn!("expr is none: {:?}", id)
      }
      ExprT::Expr(i) => {
        let value = if let Some(value) = vm.values.get(i) {
          value.clone()
        } else {
          anyhow::bail!("vm: copy value from {:?} failed", i);
        };
        vm.set_value(*id, info.ty().clone(), value);
      }
      ExprT::Func { func, this, args, send } => {
        if func.ns == "@Global" && func.name == "deploy" && args.len() == 1 {
          let contract_name = match typing.get_info_view(args.get(0).copied().unwrap()).ty() {
            Type::ContractType(name) => name,
            t => {
              anyhow::bail!("vm: deploy args not contract {:?}", t)
            }
          };
          trace!("contract name {}", contract_name);
          let bytecode = match vm.values.get(&args[0]) {
            Some(Value { value: ethabi::Token::Bytes(bytes), ..}) => bytes,
            _ => anyhow::bail!("vm: contract bytecode not present"),
          };
          let result = deploy_contract(contract_name, bytecode)?;
          vm.set_value(*id, info.ty().clone(), result.into());
        } else {
          warn!("fixme: send tx");
        }
      }
      ExprT::Number(number) => {
        warn!("fixme: number");
        let mut value = Value { value: ethabi::Token::Uint(U256::default()), ty: ethabi::ParamType::Uint(256) };
        vm.set_value(*id, info.ty().clone(), value);
      }
      ExprT::String(string) => {
        warn!("fixme: string");
        let mut value = Value { value: ethabi::Token::Bytes(string.value.clone()), ty: ethabi::ParamType::Bytes };
        vm.set_value(*id, info.ty().clone(), value);
      }
      _ => {
        warn!("skip {:?} => {:?}", id, info.expr.returns)
      }
    }
  }
  Ok(())
}

fn deploy_contract(contract_name: &str, bytecode: &[u8]) -> Result<Address> {
  info!("deploy_contract: {} {}", contract_name, bytecode.len());
  warn!("fixme: deploy");
  Ok(Address::default())
}
