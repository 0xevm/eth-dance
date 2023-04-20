use crate::{vm::{Value, ValueKind}, typing::Type};


impl Value {
  pub fn as_ty(self, ty: &Type) -> Result<Self, Self> {
    trace!("convert {} => {}", self.ty, ty);
    if &self.ty == ty {
      return Ok(self)
    }
    let result = match (&self.ty, &self.v, ty) {
      (Type::Number(_), ValueKind::Number(_), Type::Number(_)) |
      (Type::Bytes, ValueKind::Bytecode(_), Type::ContractType(_))
        => Value { ty: ty.clone(), ..self },
      _ => {
        warn!("unknown convert {} {}", self.ty, ty);
        return Err(self)
      }
    };
    Ok(result)
  }
}
