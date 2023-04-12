use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

use crate::typing::Id;
use crate::{ast::{Ident, TypedString, TypedNumber, NumberSuffix, self}, typing::{Type, ExprCode}};

impl Display for Ident {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    if self.dollar { f.write_str("$")? }
    f.write_str(&self.name)
  }
}

impl Display for TypedString {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{}{:?}", self.prefix, String::from_utf8_lossy(&self.value))
  }
}

impl Display for TypedNumber {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{}{}", self.value, self.suffix)
  }
}

impl Display for NumberSuffix {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let u = if self.is_unsigned() { "u" } else { "" };
    match self {
      NumberSuffix::None => write!(f, ""),
      NumberSuffix::Signed => write!(f, "i"),
      NumberSuffix::Q(_, i) => write!(f, "{}q{}", u, i),
      NumberSuffix::F(i) => write!(f, "f{}{}", i, u),

      NumberSuffix::E(true, 18) => write!(f, "eth"),
      NumberSuffix::E(true, 9) => write!(f, "gwei"),
      NumberSuffix::E(_, i) => write!(f, "e{}{}", i, u),
    }
  }
}

impl FromStr for NumberSuffix {
  type Err = ast::Error;

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    ast::parse_number_suffix(s, ast::Span::default())
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::NoneType => write!(f, "NoneType"),
      Type::Global(s) => write!(f, "@{}", s),
      Type::ContractType(s) => write!(f, "ContractType({})", s),
      Type::Contract(s) => write!(f, "Contract({})", s),
      Type::Function(a, b) => write!(f, "Function({}:{})", a, b),
      Type::Abi(abi) => write!(f, "Abi({})", abi),
      Type::String(s) if s.is_empty() => write!(f, "String"),
      Type::String(s) => write!(f, "Custom({})", s),
      Type::Number(s) => write!(f, "Number({})", s),
    }
  }
}

impl FromStr for Type {
  type Err = &'static str;

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    let result = match s {
      "NoneType" => Type::NoneType,
      "String" => Type::String(String::new()),
      _ if s.starts_with("@") => Type::Global(s[1..].to_string()),
      _ if s.contains("(") => {
        let mut sp = s.splitn(2, "(");
        let prefix = sp.next().unwrap();
        let suffix = sp.next().unwrap();
        let suffix = suffix.strip_suffix(")").unwrap_or(suffix);
        match prefix {
          "ContractType" => Type::ContractType(suffix.to_string()),
          "Contract" => Type::Contract(suffix.to_string()),
          "Function" => {
            let a = suffix.splitn(2, ":").collect::<Vec<_>>();
            Type::Function(a[0].to_string(), a[1].to_string())
          }
          "Abi" => Type::Abi(ethabi::param_type::Reader::read(suffix).map_err(|_| "abi parse")?),
          "Custom" => Type::String(suffix.to_string()),
          "Number" => Type::Number(suffix.parse().map_err(|_| "parse number suffix")?),
          _ => return Err("unknown prefix"),
        }
      }
      _ => return Err("unknown type")
    };
    Ok(result)
  }
}

impl std::fmt::Display for Id {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "$${}", self.0)
  }
}

impl std::fmt::Display for ExprCode {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExprCode::None => write!(f, "()"),
      ExprCode::Func { func, this, args, send, .. } => {
        let dot = if *send {":"} else {"."};
        let args_str = args.iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(", ");
        match this {
          Some(this) => f.write_str(&format!("{}[{}]{}{}({})", func.ns, this, dot, func.name, args_str)),
          None => f.write_str(&format!("{}{}{}({})", func.ns, dot, func.name, args_str)),
        }
      }
      ExprCode::Expr(arg0) => write!(f, "{}", arg0),
      ExprCode::String(arg0) => write!(f, "{}", arg0),
      ExprCode::Number(arg0) => write!(f, "{}", arg0),
    }
  }
}
impl FromStr for ExprCode {
  type Err = &'static str;

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    let result = match s {
      "()" => ExprCode::None,
      _ => unreachable!()
    };
    Ok(result)
  }
}
