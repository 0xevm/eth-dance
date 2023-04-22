use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

use ethabi::ParamType;
use ethers::signers::LocalWallet;
use ethers::utils::to_checksum;

use crate::ast::StringPrefix;
use crate::convert::conv::{try_convert_hex_to_bytes, ErrorExt};
use crate::typing::{CodeId, self};
use crate::vm::{ValueKind, Value, ValueId, ValueKey};
use crate::{ast::{Ident, TypedString, TypedNumber, NumberSuffix, self}, typing::{Type, ExprCode}};

use super::Error;
use super::conv::{try_convert_hex_to_addr, ErrorKind};

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
  /// related [`crate::typing::parse_type`]
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Type::NoneType => write!(f, "none"),
      Type::Bool => write!(f, "bool"),
      Type::String => write!(f, "string"),
      Type::Address => write!(f, "address"),
      Type::Bytes => write!(f, "bytes"),
      // Type::Custom(StringPrefix::Bytecode) | Type::Custom(StringPrefix::Contract) => write!(f, "bytecode"),
      Type::Wallet => write!(f, "wallet"),
      Type::Receipt => write!(f, "receipt"),
      Type::Global(s) => write!(f, "@{}", s),
      Type::Contract(s) => write!(f, "{:?}", s),
      // Type::Function(a, b) => write!(f, "Function({}:{})", a, b),
      Type::Abi(abi) => write!(f, "abi{:?}", abi.to_string()),
      Type::ContractType(s) => write!(f, "contract{:?}", s),
      Type::Number(s) => write!(f, "int_{}", s),
      Type::FixedArray(t, n) => write!(f, "[{}; {}]", t, n),
    }
  }
}

impl FromStr for Type {
  type Err = Error;

  fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
    use pest::Parser;
    let mut pairs = ast::AstParser::parse(ast::Rule::r#type, s).context("Type::from_str: parsing")?;
    let result = if let Some(pair) = pairs.next() {
      assert_eq!(pair.as_rule(), ast::Rule::r#type);
      let lit = ast::parse_type(pair).context("Type::from_str: ast")?;
      typing::parse_type(&lit).map_err(ErrorKind::custom_error).context("Type::from_str: typing")?
    } else {
      unreachable!();
    };
    ast::check_empty(pairs).map_err(|e| e.context("", ast::Rule::r#type)).context("Type::from_str: ast")?;
    Ok(result)
  }
}

impl std::fmt::Display for CodeId {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "$${}", self.0)
  }
}
impl std::fmt::Display for ValueId {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "$${}.{}", self.0, self.1)
  }
}
impl std::str::FromStr for CodeId {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let re = regex::Regex::new(r"\$\$(\d+)").unwrap();
    let Some(m) = re.captures(s) else {
      return Err("no match");
    };
    assert_eq!(m.len(), 2);
    if m.get(0).unwrap().as_str().len() != s.len() { return Err("extra string") }
    let id_0 = m.get(1).unwrap().as_str().parse().map_err(|_| "parse u64")?;
    Ok(CodeId(id_0))
  }
}
impl std::str::FromStr for ValueId {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let re = regex::Regex::new(r"\$\$(\d+)\.(\d+)").unwrap();
    let Some(m) = re.captures(s) else {
      return Err("no match");
    };
    assert_eq!(m.len(), 3);
    if m.get(0).unwrap().as_str().len() != s.len() { return Err("extra string") }
    let id_0 = m.get(1).unwrap().as_str().parse().map_err(|_| "parse u64")?;
    let id_1 = m.get(2).unwrap().as_str().parse().map_err(|_| "parse u64")?;
    Ok(ValueId(id_0, id_1))
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
      ExprCode::Convert(arg0, Some(arg1)) => write!(f, "{} as {}", arg0, arg1),
      ExprCode::Convert(arg0, None) => write!(f, "{}", arg0),
      ExprCode::String(arg0) => write!(f, "{}", arg0),
      ExprCode::Number(arg0) => write!(f, "{}", arg0),
      ExprCode::List(arg0) => {
        let s = arg0.iter().map(ToString::to_string).collect::<Vec<_>>();
        write!(f, "[{}]", s.join(","))
      },
      ExprCode::Loop(arg0, arg1) => write!(f, "loop: {} => {}", arg0, arg1),
      ExprCode::EndLoop(arg0) => write!(f, "end_loop: {}", arg0),
      ExprCode::Access(arg0, args) => {
        let args_str = args.iter().map(|i| format!("{}", i)).collect::<Vec<_>>().join(", ");
        write!(f, "{}[{}]", arg0, args_str)
      }
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

impl Display for Value {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match &self.v {
      ValueKind::Tuple(i) => write!(f, "({})", i.iter().map(ToString::to_string).collect::<Vec<_>>().join(", ")),
      _ => write!(f, "{}: {}", self.v.repr_str(), self.ty)
    }
  }
}

impl FromStr for Value {
  type Err = Error;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    if s == "()" {
      return Ok(Self::NONE)
    }
    if s.starts_with("(") && s.ends_with(")") {
      todo!()
    }
    let sr = s.rsplitn(2, ":").collect::<Vec<_>>();
    let ty: Type = sr[0].trim().parse()?;
    let v = ValueKind::parse_str(sr[1], &ty).context("Value::from_str")?;
    Self::new(v, ty).map_err(|e| ErrorKind::anyhow(e)).context("Value::from_str")
  }
}

impl std::fmt::Debug for ValueKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Bool(arg0) => f.debug_tuple("Bool").field(arg0).finish(),
      Self::Number(arg0) => f.debug_tuple("Number").field(arg0).finish(),
      Self::Address(arg0) => f.debug_tuple("Address").field(arg0).finish(),
      Self::Wallet(arg0) => f.debug_tuple("Wallet").field(arg0).finish(),
      Self::Receipt(arg0) => f.debug_tuple("Receipt").field(&arg0.transaction_hash).finish(),
      Self::String(arg0) => f.debug_tuple("String").field(arg0).finish(),
      Self::Bytes(arg0) => f.debug_tuple("Bytes").field(arg0).finish(),
      Self::Bytecode(arg0) => {
        // TODO: show
        f.debug_tuple("Bytecode").field(&[arg0.len()]).finish()
      }
      Self::Array(arg0, arg1) => f.debug_tuple("Array").field(arg0).field(arg1).finish(),
      Self::Tuple(arg0) => f.debug_tuple("Tuple").field(arg0).finish(),
    }
  }
}

impl ValueKind {
  pub fn repr_str(&self) -> String {
    match self {
      ValueKind::Bool(i) => format!("{}", i),
      ValueKind::Number(i) => format!("{}", i),
      ValueKind::Address(i) => format!("{}", to_checksum(i, None)),
      ValueKind::Wallet(i) => format!("0x{}", hex::encode(i.clone().signer().to_bytes())),
      ValueKind::Receipt(i) => format!("{}", serde_json::to_string(i).unwrap()),
      ValueKind::String(i) => format!("{:?}", i),
      ValueKind::Bytes(i) => format!("0x{}", hex::encode(i)),
      ValueKind::Bytecode(i) => format!("0x{}", hex::encode(i)), // TODO: hash
      ValueKind::Array(i, _) => format!("[{}]", i.iter().map(|x| x.repr_str()).collect::<Vec<_>>().join(", ")),
      ValueKind::Tuple(i) =>  format!("({})", i.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ")),
    }
  }

  pub fn parse_str(s: &str, ty: &Type) -> Result<Self, ErrorKind> {
    trace!("value parse_str {} {}", s, ty);
    let result = match ty {
      Type::NoneType => Self::Bytes(vec![]),
      Type::Global(_) => todo!(),
      Type::ContractType(_) => todo!(),
      Type::Address | Type::Contract(_) | Type::Abi(ParamType::Address) => {
        Self::Address(try_convert_hex_to_addr(s)?)
      }
      Type::Abi(_) => todo!(),
      Type::Bool => Self::Bool(s.parse()?),
      Type::String => Self::String(ron::from_str(s)?),
      Type::Bytes | Type::Wallet => {
        let bytes = try_convert_hex_to_bytes(s)?;
        match ty {
          // StringPrefix::None => unreachable!(),
          Type::Bytes => Self::Bytes(bytes),
          // StringPrefix::Bytecode => return Ok(Self::Bytecode(bytes)),
          Type::Wallet => Self::Wallet(LocalWallet::from_bytes(&bytes).unwrap()),
          // StringPrefix::Contract => todo!(),
          _ => unreachable!()
        }
      }
      Type::Receipt => Self::Receipt(serde_json::from_str(s).unwrap()),
      Type::Number(_) =>
        Self::Number(bigdecimal::BigDecimal::from_str(s).unwrap()),
      Type::FixedArray(inner, _) => {
        warn!("fixme: parse array");
        let v = s[1..s.len()-1].split(",").map(|i| Self::parse_str(i.trim(), inner.as_ref())).collect::<Result<_, _>>()?;
        Self::Array(v, inner.as_ref().clone())
      },
    };
    Ok(result)
  }
}

impl Display for ValueKey {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    match self {
      ValueKey::Idx(i) => write!(f, "${}", i),
      ValueKey::Address(addr) => write!(f, "0x{}", to_checksum(addr, None)),
      ValueKey::String(s) => write!(f, "@{}", s),
    }
  }
}
impl FromStr for ValueKey {
  type Err = &'static str;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let result = if s.starts_with("$") {
      ValueKey::Idx(s[1..].parse::<usize>().map_err(|_| "idx not number")?)
    } else if s.starts_with("0x") {
      let addr = try_convert_hex_to_addr(s).map_err(|_| "addr convert failed")?;
      ValueKey::Address(addr)
    } else if s.starts_with('@') {
      ValueKey::String(s[1..].to_string())
    } else {
      return Err("unknown value_key")
    };
    Ok(result)
  }
}
