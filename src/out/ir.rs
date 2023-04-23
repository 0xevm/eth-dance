use crate::{typing::{Typing, Type}, ast::NumberSuffix};

impl Type {
  pub fn as_abi(&self) -> Option<ethabi::ParamType> {
    Some(match self {
      Type::NoneType => ethabi::ParamType::FixedBytes(0),
      Type::Global(_) => return None,
      Type::ContractType(_) => ethabi::ParamType::Bytes,
      Type::Contract(_) | Type::ContractReceipt(_) => ethabi::ParamType::Address,
      // Type::Function(_, _) => return None,
      Type::Abi(i) => i.clone(),
      Type::Bool => ethabi::ParamType::Bool,
      Type::String => ethabi::ParamType::String,
      Type::Address | Type::Wallet => ethabi::ParamType::Address,
      Type::Bytes => ethabi::ParamType::Bytes,
      Type::Number(i) => match i {
        NumberSuffix::F(size) => ethabi::ParamType::FixedBytes(*size / 8),
        _ if i.is_unsigned() => ethabi::ParamType::Uint(256),
        _ => ethabi::ParamType::Int(256),
      },
      Type::FixedArray(i, n) => {
        ethabi::ParamType::FixedArray(Box::new(i.as_abi()?), *n)
      },
      Type::Receipt => ethabi::ParamType::FixedBytes(32),
    })
  }
}

pub fn to_ir(typing: &Typing) -> Vec<String> {
  let mut v = Vec::new();
  for (id, info) in &typing.infos {
    let abi_str = match info.expr.returns.as_abi() {
      Some(ty) => format!(": {}", ty),
      None => String::new(),
    };
    let mut s = format!("{}{} = {}", id, abi_str, info.expr.code);
    if !info.display.is_empty() {
      let comment = format!("# {}: {}", info.display, info.ty());
      s = format!("{}\n{}", comment, s);
    }
    v.push(s);
  }
  v
}
