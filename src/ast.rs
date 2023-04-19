use std::{rc::Rc, string::FromUtf8Error};

use pest::{Parser, iterators::Pair};

#[derive(Debug, thiserror::Error)]
pub enum ErrorKind {
  #[error(transparent)]
  Parse(#[from] pest::error::Error<Rule>),
  #[error("errors")]
  Errors(Vec<Error>),
  #[error("require {0:?}")]
  Require(Rule),
  #[error("require {require:?} found {found:?}")]
  Mismatch { require: Rule, found: Rule },
  #[error("require {require:?} value error: {value:?}")]
  Value { require: Rule, value: String },
  #[error("pair count {0}")]
  PairCount(usize),
  #[error("unknown {0:?}")]
  Unknown(String),
  #[error(transparent)]
  Utf8Error(#[from] FromUtf8Error),
}
#[derive(Debug, thiserror::Error)]
#[error("parsing: {message} {at:?} {rule:?}")]
pub struct Error {
  #[source]
  pub kind: ErrorKind,
  pub message: String,
  pub rule: Rule,
  pub at: Option<Span>,
  // pub backtrace: std::backtrace::Backtrace,
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

impl ErrorKind {
  fn when(self, at: &Span, rule: Rule) -> Error {
    Error { kind: self, message: String::new(), at: Some(at.clone()), rule, }
  }
  fn when_rule(self, when: Rule, rule: Rule) -> Error {
    Error { kind: self, message: format!("at rule {:?}", when), at: None, rule, }
  }
  fn context<S: ToString>(self, s: S, rule: Rule) -> Error {
    Error { kind: self, message: s.to_string(), at: None, rule, }
  }
}
pub trait ErrorExt<T, E> {
  fn when(self, at: &Span, rule: Rule) -> Result<T>;
  fn when_rule(self, when: Rule, rule: Rule) -> Result<T>;
  fn context<S: ToString>(self, s: S, rule: Rule) -> Result<T>;
}
impl<T, E: Into<ErrorKind>> ErrorExt<T, E> for Result<T, E> {
  fn when(self, at: &Span, rule: Rule) -> Result<T> {
    self.map_err(|e| e.into().when(at, rule))
  }
  fn when_rule(self, when: Rule, rule: Rule) -> Result<T> {
    self.map_err(|e| e.into().when_rule(when, rule))
  }
  fn context<S: ToString>(self, s: S, rule: Rule) -> Result<T> {
    self.map_err(|e| e.into().context(s, rule))
  }
}

impl Error {
  pub fn inner_errors(self) -> Vec<Error> {
    match self.kind {
      ErrorKind::Errors(v) => v.into_iter().map(|i| {
        i.inner_errors()
      }).flatten().collect(),
      _ => vec![self]
    }
  }
  pub fn show_pos(&self, input: &str, line_index: Rc<Vec<usize>>) -> String {
    let mut s = String::new();
    if let Some(span) = &self.at {
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
impl Into<Vec<Error>> for Error {
  fn into(self) -> Vec<Error> {
    vec![self]
  }
}
impl From<Vec<Error>> for ErrorKind {
  fn from(value: Vec<Error>) -> Self {
    ErrorKind::Errors(value)
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

pub fn into_inner_pair<T: pest::RuleType>(pair: Pair<T>) -> Result<Pair<T>, ErrorKind> {
  let mut pairs = pair.into_inner();
  let Some(pair) = pairs.next() else {
    return Err(ErrorKind::PairCount(0))
  };
  if pairs.peek().is_some() {
    return Err(ErrorKind::PairCount(pairs.count() + 1))
  };
  Ok(pair)
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
pub struct Assignment {
  pub lhs: Option<ExprLit>,
  pub equal_span: Option<Span>,
  pub rhs: ExprLit,
  pub newline_span: Option<Span>,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct Forloop {
  pub lhs: ExprLit,
  pub rhs: ExprLit,
  pub stmts: Vec<StmtKind>,
  pub span: Span,
}

#[derive(Debug)]
pub enum StmtKind {
  Comment(String),
  Assignment(Assignment),
  Forloop(Forloop),
}

impl Default for StmtKind {
  fn default() -> Self {
    Self::Comment(String::new())
  }
}

pub fn parse(input: &str) -> Result<Vec<StmtKind>>  {
  let mut pairs = AstParser::parse(Rule::FILE, input).context("parse ast", Rule::FILE)?;
  if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::FILE => {
        parse_block(pair.into_inner().next().unwrap())
      },
      // Rule::COMMENT => continue,
      _ => unreachable!(),
    }
  } else {
    Err(ErrorKind::Require(Rule::FILE)).context("parse ast", Rule::FILE)
  }
}

fn parse_block(pair: Pair<Rule>) -> Result<Vec<StmtKind>> {
  assert_eq!(pair.as_rule(), Rule::block);
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
  drain_error(result).when(&span, Rule::FILE)
}

fn parse_stmt(pair: Pair<Rule>) -> Result<StmtKind> {
  assert_eq!(pair.as_rule(), Rule::statement);
  let span = pair.as_span().into();
  let pair = into_inner_pair(pair).when(&span, Rule::statement)?;
  match pair.as_rule() {
    Rule::assignment => parse_assignment(pair).map(StmtKind::Assignment).when(&span, Rule::statement),
    _ => unreachable!(),
  }
// Rule::forloop => parse_forloop(pair).map(|i| ExprKind::Funccall(Box::new(i)))?,
}

// statement = { (item ~ "=")? ~ expr }
fn parse_assignment(pair: Pair<Rule>) -> Result<Assignment, Vec<Error>> {
  assert_eq!(pair.as_rule(), Rule::assignment);
  let span: Span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = Assignment::default();
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
    errors.push(ErrorKind::Require(Rule::expr).when(&span.clone(), Rule::statement));
    return Err(errors)
  };
  match parse_expr(pair) {
    Ok(expr) => result.rhs = expr,
    Err(e) => errors.push(e),
  }
  if errors.is_empty() {
    Ok(result)
  } else {
    Err(errors)
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

// expr = { forloop | funccall | string | number | item }
fn parse_expr_inner(pair: Pair<Rule>) -> Result<ExprKind> {
  let span = pair.as_span().into();
  let expr = match pair.as_rule() {
    Rule::funccall => parse_funccall(pair).map(|i| ExprKind::Funccall(Box::new(i)))?,
    Rule::fixed_array => parse_array(pair).map(ExprKind::List).when(&span, Rule::expr)?,
    Rule::string => parse_string_typed(pair).map(ExprKind::String)?,
    Rule::number => parse_number(pair).map(ExprKind::Number)?,
    Rule::ident => parse_ident(pair).map(ExprKind::Ident)?,
    rule => return Err(ErrorKind::Mismatch { require: Rule::expr, found: rule }).when(&span, Rule::expr),
  };
  Ok(expr)
}

// fixed_array = { "[" ~ (expr ~ ("," ~ expr)* ~ ","?)? ~ "]"}
fn parse_array(pair: Pair<Rule>) -> Result<ExprList, Vec<Error>> {
  assert_eq!(pair.as_rule(), Rule::fixed_array);
  let span: Span = pair.as_span().into();
  let pairs = pair.into_inner();
  let mut exprs = Vec::new();
  for pair in pairs {
    assert_eq!(pair.as_rule(), Rule::expr);
    exprs.push(parse_expr(pair))
  }
  let exprs = drain_error(exprs)?;
  Ok(ExprList {
    span, exprs, kind: ExprListKind::FixedArray,
  })
}

// funccall = { item? ~ dot ~ ident ~ "(" ~ args? ~ ")" }
fn parse_funccall(pair: Pair<Rule>) -> Result<Funccall> {
  assert_eq!(pair.as_rule(), Rule::funccall);
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
    (Rule::dot, s) => return Err(ErrorKind::Value { require: Rule::dot, value: s.to_string() }).when(&span, Rule::funccall),
    (rule, _) => return Err(ErrorKind::Mismatch { require: Rule::dot, found: rule }).when(&span, Rule::funccall),
  }
  funccall.dot_span = pair.as_span().into();

  let pair = pairs.next().expect("pairs: funccall => name");
  match pair.as_rule() {
    Rule::ident => funccall.name = parse_ident(pair)?,
    rule => return Err(ErrorKind::Mismatch { require: Rule::dot, found: rule}).when(&span, Rule::funccall)
  }

  if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::args => funccall.args = parse_args(pair).when(&span, Rule::funccall)?,
      rule => return Err(ErrorKind::Mismatch { require: Rule::args, found: rule }).when(&span, Rule::funccall)
    }
  }
  Ok(funccall)
}

// args = { arg ~ ("," ~ arg)* }
fn parse_args(pair: Pair<Rule>) -> Result<Vec<ExprLit>, Vec<Error>> {
  assert_eq!(pair.as_rule(), Rule::args);
  // let span = pair.as_span().into();
  let result = pair.into_inner().map(parse_arg).collect::<Vec<_>>();
  drain_error(result)
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
  trace!("parse_type: {}", s);
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
        let prefix = inner.prefix.parse().map_err(|_| ErrorKind::Unknown(inner.prefix.clone())).when_rule(Rule::ident, Rule::r#type)?;
        let s = String::from_utf8(inner.value).when(&span.clone(), Rule::r#type)?;
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
          None => return Err(ErrorKind::Value { require: Rule::escape, value: s.to_string() }.when(&span, Rule::string)),
        }
      }
      rule => return Err(ErrorKind::Mismatch { require: Rule::raw_string, found: rule }.when(&span, Rule::string)),
    }
  }
  Ok(result)
}

fn parse_string_typed(pair: Pair<Rule>) -> Result<TypedString> {
  let i = parse_string(pair)?;
  let prefix = i.prefix.parse().map_err(|_| ErrorKind::Unknown(i.prefix.clone())).when_rule(Rule::ident, Rule::string)?;
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
    rule => return Err(ErrorKind::Mismatch { require: Rule::float, found: rule }.when(&span, Rule::number))
  }

  result.suffix = if let Some(pair) = pairs.next() {
    assert_eq!(pair.as_rule(), Rule::number_suffix);
    match pair.as_rule() {
      Rule::number_suffix => parse_number_suffix(pair.as_str(), pair.as_span().into())?,
      rule => return Err(ErrorKind::Mismatch { require: Rule::number_suffix, found: rule }.when(&span, Rule::number))
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
      _ => return Err(ErrorKind::Value { require: Rule::int, value: str[1..].to_string()}.when(&span, Rule::number_suffix)),
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
    _ => return Err(ErrorKind::Value { require: Rule::number_suffix, value: str.to_string() }.when(&span, Rule::number_suffix)),
  };
  Ok(result)
}
