use std::{collections::BTreeMap, rc::Rc};

use crate::{ast::{Stmt, Expr, Span, StringPrefix, NumberSuffix, TypedExpr, Funccall}, global::{Func, globals}};

#[derive(Debug, thiserror::Error)]
pub enum Error {
  #[error("typing: {0:?}")]
  Errors(Vec<Error>),
  #[error("typing: name not found {0:?} at {1:?}")]
  NameNotFound(String, Span),
  #[error("typing: scope not contract {0:?} at {1:?}")]
  ScopeNotContract(Type, Span),
  #[error("typing: func not found {0}.{1} at {2:?}")]
  FuncNotFound(String, String, Span),
}
pub type Result<T, E=Error> = std::result::Result<T, E>;


impl Error {
  pub fn inner_errors(self) -> Vec<Self> {
    match self {
      Error::Errors(v) => v.into_iter().map(|i| i.inner_errors()).flatten().collect(),
      _ => vec![self]
    }
  }
  pub fn flatten(self) -> Self {
    match self {
      Error::Errors(v) => {
        Error::Errors(Error::Errors(v).inner_errors())
      }
      _ => self
    }

  }
  pub fn span(&self) -> Option<Span> {
    match self {
      Error::NameNotFound(_, span) |
      Error::ScopeNotContract(_, span) |
      Error::FuncNotFound(_, _, span) =>
        Some(span.clone()),
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

#[derive(Debug, Clone, Default)]
pub enum Type {
  #[default] None,
  Global,
  Contract(String),
  Function(String, String),
  Address,
  Uint(usize),
  Int(usize),
  _String(StringPrefix), // the prefix
  _Number(NumberSuffix),
}

#[derive(Debug, Default)]
pub struct Info {
  pub should: Option<Type>,
  pub got: Type,
  pub display: String,
}

impl Info {
  pub fn ty(&self) -> &Type {
    return self.should.as_ref().unwrap_or(&self.got)
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id(u64);
pub struct Typing {
  pub last_id: Id,
  pub infos: BTreeMap<Id, Info>,
  pub funcs: BTreeMap<String, BTreeMap<String, Func>>,
  pub found: BTreeMap<String, Id>,
}

impl Typing {
  pub fn new() -> Self {
    let mut funcs = BTreeMap::new();
    funcs.insert("@Global".to_string(), globals());
    Self {
      last_id: Id(0),
      infos: BTreeMap::new(),
      funcs,
      found: BTreeMap::new(),
    }
  }

  pub fn add_scope(&mut self, name: &str, scope: BTreeMap<String, Func>) {
    let id = self.new_id();
    self.found.insert(name.to_string(), id);
    self.get_info(id).should = Some(Type::Contract(name.to_string()));
    self.funcs.insert(name.to_string(), scope);
  }

  pub fn new_id(&mut self) -> Id {
    let id = Id(self.last_id.0+1);
    self.last_id = id;
    id
  }

  pub fn get_info(&mut self, id: Id) -> &mut Info {
    self.infos.entry(id).or_default()
  }

  pub fn find_name(&self, name: &str) -> Option<Id> {
    self.found.get(name).copied()
  }

  pub fn insert_name(&mut self, name: &str) -> Id {
    if name == "" {
      let id = self.new_id();
      self.get_info(id).display = format!("$${}", id.0);
      return self.new_id()
    }
    if name.starts_with("$") {
      if let Some(id) = self.found.get(name).copied() {
        return id
      }
    }

    let id = self.new_id();
    self.get_info(id).display = name.to_string();
    self.found.insert(name.to_string(), id);
    id
  }
}

pub fn parse_file(state: &mut Typing, stmts: &[Stmt]) -> Result<()> {
  let mut errors = Vec::new();
  for stmt in stmts {
    if let Err(e) = parse_stmt(state, stmt) {
      errors.push(e)
    }
  }
  if errors.is_empty() {
    Ok(())
  } else {
    Err(Error::Errors(errors))
  }
}

pub fn parse_stmt(state: &mut Typing, stmt: &Stmt) -> Result<()> {
  let name = stmt.lhs.as_ref().map(ToString::to_string).unwrap_or_default();
  let id = state.insert_name(&name);
  state.get_info(id).got = parse_expr(state, &stmt.rhs)?;
  Ok(())
}

pub fn parse_expr(state: &mut Typing, expr: &TypedExpr) -> Result<Type> {
  let result = match &expr.expr {
    Expr::Ident(i) => {
      let dst = state.find_name(&i.to_string());
      match dst {
        Some(dst) => {
          state.get_info(dst).ty().clone()
        },
        None => return Err(Error::NameNotFound(i.to_string(), i.span.clone()))
      }
    },
    Expr::Funccall(i) => {
      let func = parse_func(state, i)?;
      let args = i.args.iter().map(|t| parse_expr(state, t)).collect::<Result<Vec<_>>>()?;
      func.infer_type(args)
    },
    Expr::String(i) => {
      Type::_String(i.prefix.clone().unwrap_or_default())
    },
    Expr::Number(i) => {
      Type::_Number(i.suffix.clone())
    },
    _ => unreachable!(),
  };
  Ok(result)
}

fn parse_func(state: &mut Typing, i: &Funccall) -> Result<Func> {
  let scope = match &i.scope {
    Some(expr) => {
      parse_expr(state, expr)?
    }
    None => Type::Global,
  };
  let scope_str = match scope {
    Type::Global => "@Global".to_string(),
    Type::Contract(name) => name.clone(),
    _ => return Err(Error::ScopeNotContract(scope, i.span.clone())),
  };
  let func = state.funcs.get(&scope_str).and_then(|f| f.get(&i.name.to_string())).cloned();
  match func {
    Some(func) => Ok(func),
    None => Err(Error::FuncNotFound(scope_str, i.name.to_string(), i.span.clone())),
  }
}
