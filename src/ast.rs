use std::{rc::Rc, string::FromUtf8Error};

use pest::{Parser, iterators::Pair};

#[derive(Debug, thiserror::Error)]
pub enum Error {
  #[error("parse")]
  Parse(#[from] pest::error::Error<Rule>),
  #[error("{2:?}:{1:?}: {0:?}", )]
  Errors(Vec<Error>, Span, Rule),
  #[error("{2:?}:{1:?}: require {0:?}")]
  Require(Rule, Span, Rule),
  #[error("{at:?}:{span:?}: require {require:?} found {found:?}")]
  Mismatch { require: Rule, found: Rule, span: Span, at: Rule },
  #[error("{at:?}:{span:?}: require {require:?} value error: {value:?}")]
  Value { require: Rule, value: String, span: Span, at: Rule },
  #[error("{2:?}:{1:?}: unknown {0:?}")]
  Unknown(String, Rule, Rule),
  #[error("{2:?}:{1:?}: utf8 {0:?}")]
  Utf8Error(FromUtf8Error, Span, Rule),
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

impl Error {
  pub fn inner_errors(self) -> Vec<Self> {
    match self {
      Error::Errors(v, _, _) => v.into_iter().map(|i| i.inner_errors()).flatten().collect(),
      _ => vec![self]
    }
  }
  pub fn flatten(self) -> Self {
    match self {
      Error::Errors(v, s, r) => {
        Error::Errors(Error::Errors(v, s.clone(), r).inner_errors(), s, r)
      }
      _ => self
    }

  }
  pub fn span(&self) -> Option<Span> {
    match self {
      Error::Errors(_, span, _) |
      Error::Require(_, span, _) |
      Error::Mismatch { span, .. } |
      Error::Value { span, .. } =>
        Some(span.clone()),
      _ => None
    }
  }
  pub fn rule(&self) -> Option<Rule> {
    match self {
      Error::Errors(_, _, rule) |
      Error::Require(_, _, rule) |
      Error::Mismatch { at: rule, .. } |
      Error::Value { at: rule, .. } =>
        Some(rule.clone()),
      _ => None
    }
  }
  pub fn show_pos(&self, input: &str, line_index: Rc<Vec<usize>>) -> String {
    let mut s = String::new();
    if let Some(span) = self.span() {
      let line = match line_index.binary_search(&span.start) {
        Ok(i) => i,
        Err(i) => i.saturating_sub(1),
      };
      let col = span.start - line_index[line];
      s = format!("{}:{}: {}", line+1, col+1, &input[span.start..span.start+span.len])
    }
    s
  }
}

pub fn drain_error<T>(items: Vec<Result<T>>) -> Result<Vec<T>, Vec<Error>> {
  let mut result = Vec::new();
  let mut errors = Vec::new();
  for i in items {
    match i {
      Ok(i) => result.push(i),
      Err(e) => errors.push(e),
    }
  }
  if errors.is_empty() {
    Ok(result)
  } else {
    return Err(errors);
  }
}

#[derive(Parser)]
#[grammar = "parser.pest"] // relative to src
pub struct AstParser;

#[derive(Debug, Clone, Default)]
pub struct Span {
  pub start: usize,
  pub len: usize,
}

impl From<pest::Span<'_>> for Span {
  fn from(value: pest::Span) -> Self {
    Self {
      start: value.start(),
      len: value.end() - value.start(),
    }
  }
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Accessor {
  #[default] Dot, Colon,
}
impl Accessor {
  pub fn is_send(self) -> bool {
    match self {
      Accessor::Dot => false,
      Accessor::Colon => true,
    }
  }
}

#[derive(Debug, Default)]
pub struct Ident {
  pub dollar: bool,
  pub dollar_span: Span,
  pub name: String,
  pub span: Span,
}

#[derive(Debug, Default)]
pub enum TypeKind {
  #[default] None,
  Ident(String),
  String(String, TypePrefix),
  Array(Box<TypeLit>, Option<usize>),
}

#[derive(Debug, Default)]
pub struct TypeLit {
  pub kind: TypeKind,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct ExprLit {
  pub inner: ExprKind,
  pub hint: Option<TypeLit>, // TODO Type::from_str
  pub span: Span,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, )]
pub enum ExprListKind {
  #[default] Raw, FixedArray,
}

#[derive(Debug, Default)]
pub struct ExprList {
  pub exprs: Vec<ExprLit>,
  pub kind: ExprListKind,
  pub span: Span,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum NumberSuffix {
  #[default] None, Signed, Q(bool, usize), F(usize), E(bool, usize),
}

#[derive(Debug, Clone, Default)]
pub struct TypedNumber {
  pub value: String,
  pub value_span: Span,
  pub suffix: NumberSuffix,
  pub suffix_span: Span,
  pub span: Span,
}

impl NumberSuffix {
  pub fn is_unsigned(self) -> bool {
    match self {
      NumberSuffix::None => true,
      NumberSuffix::Signed | NumberSuffix::F(_) => false,
      NumberSuffix::E(b, _) | NumberSuffix::Q(b, _)
        => b
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, strum::Display, strum::EnumString)]
#[strum(serialize_all = "snake_case")]
pub enum StringPrefix {
  #[default]
  #[strum(serialize = "", serialize = "string")]
  None,
  #[strum(serialize = "byte", serialize = "b")]
  Byte,
  Bytecode, Hex, Key, Address, Contract,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, strum::Display, strum::EnumString)]
#[strum(serialize_all = "snake_case")]
pub enum TypePrefix {
  #[default]
  #[strum(serialize = "", serialize = "string")]
  None,
  Abi, Contract,
}

impl StringPrefix {
  pub fn is_empty(self) -> bool {
    self == StringPrefix::None
  }
}

#[derive(Debug, Clone, Default)]
pub struct StringLit {
  pub prefix: String,
  pub value: Vec<u8>,
  // pub value_span: Span,
  pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct TypedString {
  pub prefix: StringPrefix,
  pub value: Vec<u8>,
  // pub value_span: Span,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct Funccall {
  pub scope: Ident,
  pub dot: Accessor,
  pub name: Ident,
  pub args: Vec<ExprLit>,
  pub dot_span: Span,
  pub args_span: Span,
  pub span: Span,
}

#[derive(Debug, Default)]
pub enum ExprKind {
  #[default] None,
  Ident(Ident),
  Funccall(Box<Funccall>),
  String(TypedString),
  Number(TypedNumber),
  List(ExprList),
}

#[derive(Debug, Default)]
pub struct Stmt {
  pub lhs: Option<ExprLit>,
  pub equal_span: Option<Span>,
  pub rhs: ExprLit,
  pub newline_span: Option<Span>,
  pub span: Span,
}

pub fn parse(input: &str) -> Result<Vec<Stmt>>  {
  let mut pairs = AstParser::parse(Rule::FILE, input)?;
  if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::FILE => parse_file(pair),
      // Rule::COMMENT => continue,
      _ => unreachable!(),
    }
  } else {
    Err(Error::Require(Rule::FILE, Span::default(), Rule::FILE))
  }
}

fn parse_file(pair: Pair<Rule>) -> Result<Vec<Stmt>> {
  let span = pair.as_span().into();
  let pairs = pair.into_inner();
  let mut result = Vec::new();
  for pair in pairs {
    match pair.as_rule() {
      Rule::statement => result.push(parse_stmt(pair)),
      Rule::COMMENT | Rule::EOI => {},
      _ => unreachable!(),
    }
  }
  drain_error(result).map_err(|e| Error::Errors(e, span, Rule::FILE))
}

// statement = { (item ~ "=")? ~ expr }
fn parse_stmt(pair: Pair<Rule>) -> Result<Stmt> {
  let span: Span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = Stmt::default();
  let pair = pairs.peek();
  let mut errors = Vec::new();
  match pair.as_ref().map(Pair::as_rule) {
    Some(Rule::item) => {
      match parse_item(pairs.next().unwrap()) {
        Ok(expr) => result.lhs = Some(expr),
        Err(e) => errors.push(e)
      }
    }
    _ => {},
  }
  let Some(pair) = pairs.next() else {
    errors.push(Error::Require(Rule::expr, span.clone(), Rule::statement));
    return Err(Error::Errors(errors, span, Rule::statement))
  };
  match parse_expr(pair) {
    Ok(expr) => result.rhs = expr,
    Err(e) => errors.push(e),
  }
  if errors.is_empty() {
    Ok(result)
  } else {
    Err(Error::Errors(errors, span, Rule::statement))
  }
}

fn parse_expr(pair: Pair<Rule>) -> Result<ExprLit> {
  assert_eq!(pair.as_rule(), Rule::expr);
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let expr = parse_expr_inner(pairs.next().expect("pairs: expr => inner"))?;
  Ok(ExprLit {
    inner: expr, span, hint: None,
  })
}

// expr = { funccall | string | number | item }
fn parse_expr_inner(pair: Pair<Rule>) -> Result<ExprKind> {
  let span = pair.as_span().into();
  let expr = match pair.as_rule() {
    Rule::funccall => parse_funccall(pair).map(|i| ExprKind::Funccall(Box::new(i)))?,
    Rule::fixed_array => parse_array(pair).map(ExprKind::List)?,
    Rule::string => parse_string_typed(pair).map(ExprKind::String)?,
    Rule::number => parse_number(pair).map(ExprKind::Number)?,
    Rule::ident => parse_ident(pair).map(ExprKind::Ident)?,
    rule => return Err(Error::Mismatch { require: Rule::expr, found: rule, span, at: Rule::expr }),
  };
  Ok(expr)
}

// fixed_array = { "[" ~ (expr ~ ("," ~ expr)* ~ ","?)? ~ "]"}
fn parse_array(pair: Pair<Rule>) -> Result<ExprList> {
  assert_eq!(pair.as_rule(), Rule::fixed_array);
  let span: Span = pair.as_span().into();
  let pairs = pair.into_inner();
  let mut exprs = Vec::new();
  for pair in pairs {
    assert_eq!(pair.as_rule(), Rule::expr);
    exprs.push(parse_expr(pair))
  }
  let exprs = drain_error(exprs).map_err(|e| Error::Errors(e, span.clone(), Rule::fixed_array))?;
  Ok(ExprList {
    span, exprs, kind: ExprListKind::FixedArray,
  })
}

// funccall = { item? ~ dot ~ ident ~ "(" ~ args? ~ ")" }
fn parse_funccall(pair: Pair<Rule>) -> Result<Funccall> {
  let span: Span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut funccall = Funccall::default();
  funccall.span = span.clone();
  if pairs.peek().expect("pairs: funccall => item").as_rule() != Rule::dot {
    funccall.scope = parse_ident(pairs.next().expect("pairs: funccall => item"))?;
  }
  let pair = pairs.next().expect("pairs: funccall => dot");
  match (pair.as_rule(), pair.as_str()) {
    (Rule::dot, ".") => funccall.dot = Accessor::Dot,
    (Rule::dot, ":") => funccall.dot = Accessor::Colon,
    (Rule::dot, s) => return Err(Error::Value { require: Rule::dot, value: s.to_string(), span, at: Rule::funccall }),
    (rule, _) => return Err(Error::Mismatch { require: Rule::dot, found: rule, span, at: Rule::funccall }),
  }
  funccall.dot_span = pair.as_span().into();

  let pair = pairs.next().expect("pairs: funccall => name");
  match pair.as_rule() {
    Rule::ident => funccall.name = parse_ident(pair)?,
    rule => return Err(Error::Mismatch { require: Rule::dot, found: rule, span, at: Rule::funccall })
  }

  if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::args => funccall.args = parse_args(pair)?,
      rule => return Err(Error::Mismatch { require: Rule::args, found: rule, span, at: Rule::funccall })
    }
  }
  Ok(funccall)
}

// args = { arg ~ ("," ~ arg)* }
fn parse_args(pair: Pair<Rule>) -> Result<Vec<ExprLit>> {
  assert_eq!(pair.as_rule(), Rule::args);
  let span = pair.as_span().into();
  let result = pair.into_inner().map(parse_arg).collect::<Vec<_>>();
  drain_error(result).map_err(|e| Error::Errors(e, span, Rule::args))
}

// arg = { expr ~ (":" ~ type)? }
fn parse_arg(pair: Pair<Rule>) -> Result<ExprLit> {
  assert_eq!(pair.as_rule(), Rule::arg);
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut expr = parse_expr(pairs.next().expect("pairs: arg => expr"))?;
  if let Some(pair) = pairs.next() {
    expr.hint = Some(parse_type(pair)?);
  }
  expr.span = span;
  assert!(pairs.next().is_none());
  Ok(expr)
}

// item = { ident ~ (":" ~ type)? }
fn parse_item(pair: Pair<Rule>) -> Result<ExprLit> {
  assert_eq!(pair.as_rule(), Rule::item);
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = ExprLit::default();
  let pair = pairs.next().expect("pairs: item => ident");
  let ident = parse_ident(pair)?;
  result.inner = ExprKind::Ident(ident);
  if let Some(pair) = pairs.next() {
    result.hint = Some(parse_type(pair)?);
  }
  result.span = span;
  Ok(result)
}

fn parse_ident(pair: Pair<Rule>) -> Result<Ident> {
  assert_eq!(pair.as_rule(), Rule::ident);
  let mut result = Ident::default();
  result.dollar_span.start = pair.as_span().start();
  if pair.as_str().starts_with('$') {
    result.dollar = true;
    result.dollar_span.len = 1;
    result.name = pair.as_str()[1..].to_string()
  } else {
    result.name = pair.as_str().to_string()
  }
  result.span = pair.as_span().into();
  Ok(result)
}

// type = {
//   ident | string |
//   "[" ~ type ~ (";" ~ int)? ~ "]"
// }
pub fn parse_type(pair: Pair<Rule>) -> Result<TypeLit> {
  assert_eq!(pair.as_rule(), Rule::r#type);
  let span: Span = pair.as_span().into();
  let s = pair.as_str().trim();
  warn!("parse_type: {}", s);
  let mut pairs = pair.into_inner();
  let kind = if s.starts_with("[") {
    let pair = pairs.next().expect("pairs: type('[') => type");
    assert_eq!(pair.as_rule(), Rule::r#type);
    let inner = parse_type(pair)?;
    let size = match pairs.next() {
      Some(pair) => {
        assert_eq!(pair.as_rule(), Rule::int);
        Some(pair.as_str().trim().parse::<usize>().expect("parse int"))
      }
      _ => None,
    };
    TypeKind::Array(Box::new(inner), size)
  } else if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::ident => TypeKind::Ident(pair.as_str().to_string()),
      Rule::string => {
        let inner = parse_string(pair)?;
        let prefix = inner.prefix.parse().map_err(|_| Error::Unknown(inner.prefix.clone(), Rule::ident, Rule::r#type))?;
        let s = String::from_utf8(inner.value).map_err(|e| Error::Utf8Error(e, span.clone(), Rule::r#type))?;
        TypeKind::String(s, prefix)
      }
      _ => unreachable!()
    }
  } else {
    unreachable!()
  };

  Ok(TypeLit { kind, span })
}

// string = ${ ident? ~ "\"" ~ (raw_string | escape)* ~ "\"" }
fn parse_string(pair: Pair<Rule>) -> Result<StringLit> {
  assert_eq!(pair.as_rule(), Rule::string);
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = StringLit::default();
  if pairs.peek().as_ref().map(|i| i.as_rule()) == Some(Rule::ident) {
    result.prefix = parse_ident(pairs.next().expect("pairs: string => ident"))?.to_string();
  }
  for pair in pairs {
    let s = pair.as_str();
    match pair.as_rule() {
      Rule::raw_string => result.value.extend(s.as_bytes()),
      Rule::escape => {
        let c = match s.chars().nth(1) {
          // predefined = { "n" | "r" | "t" | "\\" | "0" | "\"" | "'" }
          Some(c) if ['n', 'r', 't', '\\', '0', '\"', '\''].contains(&c) => Some(match c {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '0' => '\0',
            c => c
          }),
          Some('x') | Some('u') => u32::from_str_radix(&s[2..], 16).ok().and_then(char::from_u32),
          _ => None,
        };
        match c {
          Some(c) => result.value.extend(c.to_string().as_bytes()),
          None => return Err(Error::Value { require: Rule::escape, value: s.to_string(), span, at: Rule::string }),
        }
      }
      rule => return Err(Error::Mismatch { require: Rule::raw_string, found: rule, span, at: Rule::string }),
    }
  }
  Ok(result)
}

fn parse_string_typed(pair: Pair<Rule>) -> Result<TypedString> {
  let i = parse_string(pair)?;
  let prefix = i.prefix.parse().map_err(|_| Error::Unknown(i.prefix.clone(), Rule::ident, Rule::string))?;
  Ok(TypedString { prefix, value: i.value, span: i.span })
}

// number = { (float | int) ~ number_suffix? }
fn parse_number(pair: Pair<Rule>) -> Result<TypedNumber> {
  assert_eq!(pair.as_rule(), Rule::number);
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = TypedNumber::default();

  let pair = pairs.next().expect("pairs: number => int");
  match pair.as_rule() {
    Rule::float | Rule::int => result.value = pair.as_str().to_string(),
    rule => return Err(Error::Mismatch { require: Rule::float, found: rule, span, at: Rule::number })
  }

  result.suffix = if let Some(pair) = pairs.next() {
    assert_eq!(pair.as_rule(), Rule::number_suffix);
    match pair.as_rule() {
      Rule::number_suffix => parse_number_suffix(pair.as_str(), pair.as_span().into())?,
      rule => return Err(Error::Mismatch { require: Rule::number_suffix, found: rule, span, at: Rule::number })
    }
  } else {
    NumberSuffix::None
  };
  Ok(result)
}

pub(crate) fn parse_number_suffix(str: &str, span: Span) -> Result<NumberSuffix> {
  match str {
    "" => return Ok(NumberSuffix::None),
    "i" => return Ok(NumberSuffix::Signed),
    "eth" => return Ok(NumberSuffix::E(true, 18)),
    "gwei" => return Ok(NumberSuffix::E(true, 9)),
    _ => {}
  }
  let is_u = str.starts_with("u") || str.ends_with("u");
  let str = str.trim_matches('u');
  let n = if str.len() > 1 {
    match usize::from_str_radix(&str[1..], 10) {
      Ok(n) => Some(n),
      _ => return Err(Error::Value { require: Rule::int, value: str[1..].to_string(), span, at: Rule::number_suffix }),
    }
  } else { None };
  let result = match str.chars().nth(0) {
    Some('f') => {
      if is_u {
        warn!("fixme: f cannot with u, error")
      }
      NumberSuffix::F(n.unwrap_or(64))
    },
    Some('q') => NumberSuffix::Q(is_u, n.unwrap_or(64)),
    Some('e') => NumberSuffix::E(is_u, n.unwrap_or(0)),
    _ => return Err(Error::Value { require: Rule::number_suffix, value: str.to_string(), span, at: Rule::number_suffix }),
  };
  Ok(result)
}
