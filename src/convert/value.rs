use ethabi::ParamType;
use ethers::types::TransactionReceipt;

use crate::{vm::{Value, ValueKind}, typing::Type};


impl Value {
  pub fn as_ty(self, ty: &Type) -> Result<Self, Self> {
    trace!("convert {} => {}", self.ty, ty);
    if &self.ty == ty {
      return Ok(self)
    }
    let result = match (&self.ty, &self.v, ty) {
      (Type::Number(_), ValueKind::Number(_), Type::Number(_)) |
      (Type::Bytes, ValueKind::Bytecode(_), Type::ContractType(_)) |
      (Type::Address, ValueKind::Address(_), Type::Contract(_)) |
      (Type::Contract(_), ValueKind::Address(_), Type::Abi(ParamType::Address))
        => Value { ty: ty.clone(), ..self },

      (Type::Receipt, ValueKind::Receipt(TransactionReceipt { contract_address: Some(_), ..}), Type::Contract(s))
        => Value { ty: Type::ContractReceipt(s.clone()), ..self },
      _ => {
        warn!("unknown convert (as_ty) {} {}: {}", self.ty, ty, self.show());
        return Err(self)
      }
    };
    Ok(result)
  }
}
