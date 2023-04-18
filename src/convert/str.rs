use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

use ethers::signers::LocalWallet;
use ethers::utils::to_checksum;

use crate::ast::StringPrefix;
use crate::typing::Id;
use crate::vm::ValueKind;
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

impl StringPrefix {
  pub fn as_str(self) -> &'static str {
    match self {
      StringPrefix::None => "",
      StringPrefix::Byte => "b",
      StringPrefix::Bytecode => "bytecode",
      StringPrefix::Address => "address",
      StringPrefix::Contract => "contract",
      StringPrefix::Hex => "hex",
      StringPrefix::Key => "key",
    }
  }
}

impl Display for StringPrefix {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.as_str())
  }
}

impl FromStr for StringPrefix {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let result = match s {
      "" => StringPrefix::None,
      "byte" | "b" => StringPrefix::Byte,
      "bytecode" => StringPrefix::Bytecode,
      "address" => StringPrefix::Address,
      "contract" => StringPrefix::Contract,
      "hex" => StringPrefix::Hex,
      "key" => StringPrefix::Key,
      _ => return Err("unknown string prefix"),
    };
    Ok(result)
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

pub fn escape_str(s: &str) -> String {
  let s = s.replace("\\", "\\\\")
    .replace("\"", "\\\"")
    .replace("\n", "\\n")
    .replace("\t", "\\t")
    .replace(":", "\\x3A")
    .replace(",", "\\x2C");
  format!("\"{}\"", s)
}

pub fn unescape_str(s: &str) -> Result<String, &'static str> {
  let s = if s.starts_with("\"") && s.ends_with("\"") {
    s.strip_prefix("\"").unwrap_or(s).strip_suffix("\"").unwrap_or(s)
  } else { s };
  let s = s
    .replace("\\\\", "\0")
    .replace("\\\"", "\"")
    .replace("\\n", "\n")
    .replace("\\t", "\t")
    .replace("\\x3A", ":")
    .replace("\\x2C", ",")
    .replace("\0", "\\");
  Ok(s)
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::NoneType => write!(f, "none"),
      Type::Bool => write!(f, "bool"),
      Type::String(StringPrefix::None) => write!(f, "string"),
      Type::String(StringPrefix::Address) => write!(f, "address"),
      Type::String(StringPrefix::Byte) | Type::String(StringPrefix::Hex) => write!(f, "bytes"),
      Type::String(StringPrefix::Bytecode) | Type::String(StringPrefix::Contract) => write!(f, "bytecode"),
      Type::String(StringPrefix::Key) => write!(f, "wallet"),
      Type::Global(s) => write!(f, "@{}", s),
      Type::Contract(s) => write!(f, "{}", s),
      // Type::Function(a, b) => write!(f, "Function({}:{})", a, b),
      Type::Abi(abi) => write!(f, "abi{:?}", abi.to_string()),
      Type::ContractType(s) => write!(f, "contract{:?}", s),
      Type::Number(s) => write!(f, "int_{}", s),
      Type::FixedArray(t, n) => write!(f, "[{}; {}]", t, n),
    }
  }
}

impl FromStr for Type {
  type Err = &'static str;

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    let result = match s {
      "none" => Type::NoneType,
      "bool" => Type::Bool,
      "string" => Type::String(StringPrefix::None),
      "address" => Type::String(StringPrefix::Address),
      "wallet" => Type::String(StringPrefix::Key),
      "bytes" => Type::String(StringPrefix::Byte),
      "bytecode" => Type::String(StringPrefix::Bytecode),
      _ if s.starts_with("@/") => Type::Contract(s.to_string()),
      _ if s.starts_with("@") => Type::Global(s[1..].to_string()),
      _ if s.starts_with("abi\"") => {
        let inner = unescape_str(&s["abi".len()..])?;
        Type::Abi(ethabi::param_type::Reader::read(&inner).map_err(|_| "parse abi type")?)
      },
      _ if s.starts_with("contract\"") => Type::Contract(unescape_str(&s["contract".len()..])?),
      _ if s.starts_with("int_") => {
        Type::Number(s[4..].parse().map_err(|_| "parse number suffix")?)
      },
      _ if s.starts_with("[") && s.ends_with("]") => {
        let a = s[1..s.len()-1].rsplitn(2, ";").collect::<Vec<_>>();
        if a.len() != 2 {
          return Err("parse fixed_array args len")
        }
        Type::FixedArray(
          Box::new(a[1].trim().parse().map_err(|_| "parse fixed_array inner type")?),
          a[0].trim().parse().map_err(|_| "parse fixed_array count")?,
        )
      }
      _ => {
        warn!("unknown type {}", s);
        return Err("unknown type")
      }
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
      ExprCode::List(arg0) => {
        let s = arg0.iter().map(ToString::to_string).collect::<Vec<_>>();
        write!(f, "[{}]", s.join(","))
      },
    }
  }
}
// impl FromStr for ExprCode {
//   type Err = &'static str;

//   fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
//     let result = match s {
//       "()" => ExprCode::None,
//       _ => unreachable!()
//     };
//     Ok(result)
//   }
// }

impl Display for ValueKind {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      ValueKind::Tuple(i) => write!(f, "({})", i.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")),
      _ => write!(f, "{}: {}", self.value_str(), self.ty())
    }
  }
}

impl FromStr for ValueKind {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    if s.starts_with("(") && s.ends_with(")") {
      todo!()
    }
    let sr = s.rsplitn(2, ":").collect::<Vec<_>>();
    let ty: Type = sr[0].trim().parse()?;
    Self::parse_str(sr[1], &ty)
  }
}

impl ValueKind {
  pub fn value_str(&self) -> String {
    match self {
      ValueKind::Bool(i) => format!("{}", i),
      ValueKind::Number(i, _) => format!("{}", i),
      ValueKind::Address(i, _) => format!("{}", to_checksum(i, None)),
      ValueKind::Wallet(i) => format!("0x{}", hex::encode(i.clone().signer().to_bytes())),
      ValueKind::String(i) => format!("{:?}", i),
      ValueKind::Bytes(i) => format!("0x{}", hex::encode(i)),
      ValueKind::Bytecode(i) => format!("0x{}", hex::encode(i)), // TODO: hash
      ValueKind::FixedArray(i, _, _) | ValueKind::Array(i, _) => format!("[{}]", i.iter().map(|x| x.value_str()).collect::<Vec<_>>().join(", ")),
      ValueKind::Tuple(i) =>  format!("({})", i.iter().map(|x| x.value_str()).collect::<Vec<_>>().join(", ")),
    }
  }

  pub fn parse_str(s: &str, ty: &Type) -> Result<Self, &'static str> {
    trace!("value parse_str {} {}", s, ty);
    let result = match ty {
      Type::NoneType => return Ok(Self::Bytes(vec![])),
      Type::Global(_) => todo!(),
      Type::ContractType(_) => todo!(),
      Type::Contract(_) => todo!(),
      Type::Abi(_) => todo!(),
      Type::Bool => match s {
        "true" => return Ok(Self::Bool(true)),
        "false" => return Ok(Self::Bool(false)),
        _ => {},
      },
      Type::String(StringPrefix::None) => return Ok(Self::String(unescape_str(s)?)),
      Type::String(prefix) => {
        let bytes = hex::decode(s.strip_prefix("0x").unwrap_or(s)).unwrap();
        match prefix {
          StringPrefix::None => unreachable!(),
          StringPrefix::Byte | StringPrefix::Hex =>
            return Ok(Self::Bytes(bytes)),
          StringPrefix::Bytecode => return Ok(Self::Bytecode(bytes)),
          StringPrefix::Key => return Ok(Self::Wallet(LocalWallet::from_bytes(&bytes).unwrap())),
          StringPrefix::Address => {
            let mut b = [0u8; 20];
            b.copy_from_slice(&bytes);
            return Ok(Self::Address(b.into(), None))
          }
          StringPrefix::Contract => todo!(),
        }
      }
      Type::Number(suffix) =>
        return Ok(Self::Number(bigdecimal::BigDecimal::from_str(s).unwrap(), *suffix)),
      Type::FixedArray(inner, n) => {
        warn!("fixme: parse array");
        let v = s[1..s.len()-1].split(",").map(|i| Self::parse_str(i.trim(), inner.as_ref())).collect::<Result<_, _>>()?;
        return Ok(Self::FixedArray(v, inner.as_ref().clone(), *n));
      },
    };
    Err("cannot convert")
  }
}
