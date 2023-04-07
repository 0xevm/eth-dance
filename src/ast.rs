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
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

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
struct AstParser;

#[derive(Debug, Clone, Default)]
pub struct Span {
  pub start: usize,
  pub len: usize,
}

impl From<pest::Span<'_>> for Span {
  fn from(value: pest::Span) -> Self {
    Self { start: value.start(), len: value.end() - value.start() }
  }
}

#[derive(Debug, Default)]
pub enum Accessor {
  #[default] Dot, Colon,
}

#[derive(Debug, Default)]
pub struct Ident {
  pub dollar: bool,
  pub dollar_span: Span,
  pub name: String,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct TypedExpr {
  pub expr: Expr,
  pub ty: String,
  pub span: Span,
}

#[derive(Debug, Default)]
pub enum NumberSuffix {
  #[default] None, Q(bool, usize), F(bool, usize), D(bool, usize),
}

#[derive(Debug, Default)]
pub struct TypedNumber {
  pub value: String,
  pub value_span: Span,
  pub suffix: NumberSuffix,
  pub suffix_span: Span,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct TypedString {
  pub prefix: Option<Ident>,
  pub value: Vec<u8>,
  // pub value_span: Span,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct Funccall {
  pub head: Option<TypedExpr>,
  pub dot: Accessor,
  pub name: Ident,
  pub args: Vec<TypedExpr>,
  pub dot_span: Span,
  pub args_span: Span,
}

#[derive(Debug, Default)]
pub enum Expr {
  #[default] None,
  Ident(Ident),
  Funccall(Box<Funccall>),
  String(TypedString),
  Number(TypedNumber),
}

#[derive(Debug, Default)]
pub struct Stmt {
  pub lhs: Option<Ident>,
  pub equal_span: Option<Span>,
  pub rhs: TypedExpr,
  pub newline_span: Option<Span>,
  pub span: Span,
}

pub fn parse(input: &str) -> Result<Vec<Stmt>>  {
  let mut pairs = AstParser::parse(Rule::file, input)?;
  if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::file => parse_file(pair),
      // Rule::COMMENT => continue,
      _ => unreachable!(),
    }
  } else {
    Err(Error::Require(Rule::file, Span::default(), Rule::file))
  }
}

fn parse_file(pair: Pair<Rule>) -> Result<Vec<Stmt>> {
  let span = pair.as_span().into();
  let pairs = pair.into_inner();
  let mut result = Vec::new();
  for pair in pairs {
    match pair.as_rule() {
      Rule::statement => result.push(parse_stmt(pair)),
      Rule::COMMENT => {}
      _ => unreachable!(),
    }
  }
  drain_error(result).map_err(|e| Error::Errors(e, span, Rule::file))
}

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
  let Some(mut pair) = pairs.next() else {
    errors.push(Error::Require(Rule::expr, span.clone(), Rule::statement));
    return Err(Error::Errors(errors, span, Rule::statement))
  };
  if pair.as_rule() == Rule::expr {
    pair = pair.into_inner().next().expect("expr should have at least one token");
  }
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

// expr = { funccall | string | number | item }
fn parse_expr(pair: Pair<Rule>) -> Result<TypedExpr> {
  let span = pair.as_span().into();
  let expr = match pair.as_rule() {
    Rule::funccall => parse_funccall(pair).map(|i| Expr::Funccall(Box::new(i))),
    Rule::string => parse_string(pair).map(Expr::String),
    Rule::number => parse_number(pair).map(Expr::Number),
    Rule::item => parse_item(pair).map(Expr::Ident),
    rule => return Err(Error::Mismatch { require: Rule::expr, found: rule, span, at: Rule::expr }),
  };
  let expr = expr?;
  Ok(TypedExpr {
    expr,
    ty: String::new(),
    span,
  })
}

// funccall = { item? ~ dot ~ ident ~ "(" ~ args? ~ ")" }
fn parse_funccall(pair: Pair<Rule>) -> Result<Funccall> {
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut funccall = Funccall::default();
  if pairs.peek().expect("pairs: funccall => item").as_rule() != Rule::dot {
    funccall.head = Some(parse_expr(pairs.next().expect("pairs: funccall => item"))?);
  }
  let pair = pairs.next().expect("pairs: funccall => dot");
  match (pair.as_rule(), pair.as_str()) {
    (Rule::dot, ".") => funccall.dot = Accessor::Dot,
    (Rule::dot, ":") => funccall.dot = Accessor::Colon,
    (Rule::dot, s) => return Err(Error::Value { require: Rule::dot, value: s.to_string(), span, at: Rule::funccall }),
    (rule, _) => return Err(Error::Mismatch { require: Rule::dot, found: rule, span, at: Rule::funccall }),
  }

  let pair = pairs.next().expect("pairs: funccall => name");
  match pair.as_rule() {
    Rule::ident => funccall.name = parse_item(pair)?,
    rule => return Err(Error::Mismatch { require: Rule::dot, found: rule, span, at: Rule::funccall })
  }

  let pair = pairs.next().expect("pairs: funccall => args");
  match pair.as_rule() {
    Rule::args => funccall.args = parse_args(pair)?,
    rule => return Err(Error::Mismatch { require: Rule::args, found: rule, span, at: Rule::funccall })
  }
  Ok(funccall)
}

fn parse_args(pair: Pair<Rule>) -> Result<Vec<TypedExpr>> {
  let span = pair.as_span().into();
  let result = pair.into_inner().map(parse_expr).collect::<Vec<_>>();
  drain_error(result).map_err(|e| Error::Errors(e, span, Rule::args))
}

fn parse_item(pair: Pair<Rule>) -> Result<Ident> {
  let mut result = Ident::default();
  if pair.as_str().starts_with('$') {
    result.dollar = true;
    result.dollar_span = Span {
      start: pair.as_span().start(),
      len: 1,
    };
    result.name = pair.as_str()[1..].to_string()
  } else {
    result.name = pair.as_str().to_string()
  }
  result.span = pair.as_span().into();
  Ok(result)
}

// string = ${ ident? ~ "\"" ~ (raw_string | escape)* ~ "\"" }
fn parse_string(pair: Pair<Rule>) -> Result<TypedString> {
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = TypedString::default();
  if pairs.peek().as_ref().map(|i| i.as_rule()) == Some(Rule::ident) {
    result.prefix = Some(parse_item(pairs.next().expect("pairs: string => ident"))?)
  }
  for pair in pairs {
    let s = pair.as_str();
    match pair.as_rule() {
      Rule::raw_string => result.value.extend(s.as_bytes()),
      Rule::escape => {
        let c = match s.chars().nth(1) {
          // predefined = { "n" | "r" | "t" | "\\" | "0" | "\"" | "'" }
          Some(c) if ['n', 'r', 't', '\\', '0', '\"', '\''].contains(&c) => Some(c),
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

// number = { (float | int) ~ number_suffix? }
fn parse_number(pair: Pair<Rule>) -> Result<TypedNumber> {
  let span = pair.as_span().into();
  let mut pairs = pair.into_inner();
  let mut result = TypedNumber::default();

  let pair = pairs.next().expect("pairs: number => int");
  match pair.as_rule() {
    Rule::float | Rule::int => result.value = pair.as_str().to_string(),
    rule => return Err(Error::Mismatch { require: Rule::float, found: rule, span, at: Rule::number })
  }

  result.suffix = if let Some(pair) = pairs.next() {
    match pair.as_rule() {
      Rule::number_suffix => parse_number_suffix(pair.as_str(), pair.as_span().into())?,
      rule => return Err(Error::Mismatch { require: Rule::number_suffix, found: rule, span, at: Rule::number })
    }
  } else {
    NumberSuffix::None
  };
  Ok(result)
}

fn parse_number_suffix(str: &str, span: Span) -> Result<NumberSuffix> {
  let is_u = str.starts_with("u");
  let str = str.strip_prefix("u").unwrap_or(str);
  let n = if str.len() > 1 {
    match usize::from_str_radix(&str[1..], 10) {
      Ok(n) => Some(n),
      _ => return Err(Error::Value { require: Rule::int, value: str[1..].to_string(), span, at: Rule::number_suffix }),
    }
  } else { None };
  let result = match str.chars().nth(0) {
    Some('f') => NumberSuffix::F(is_u, n.unwrap_or(256)),
    Some('q') => NumberSuffix::Q(is_u, n.unwrap_or(64)),
    Some('d') => NumberSuffix::Q(is_u, n.unwrap_or(18)),
    _ => return Err(Error::Value { require: Rule::number_suffix, value: str.to_string(), span, at: Rule::number_suffix }),
  };
  Ok(result)
}
