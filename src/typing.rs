use std::{collections::BTreeMap, rc::Rc};

use crate::{
  ast::{Stmt, ExprKind, Span, StringPrefix, NumberSuffix, Expr, Funccall, TypedNumber, TypedString},
  global::{Func, globals},
};

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
  #[error("typing: infer type failed {0:?} at {1:?}")]
  InferTypeFailed(Func, Span),
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
  #[default] NoneType,
  Global,
  Contract(String),
  Function(String, String),
  Abi(ethabi::param_type::ParamType),
  String(StringPrefix), // the prefix
  Number(NumberSuffix),
}

#[derive(Default)]
pub enum ExprT {
  #[default] None,
  Func { func: Func, abi: Option<Rc<ethabi::Function>>, this: Option<Id>, args: Vec<Id>, send: bool },
  Expr(Id),
  String(TypedString),
  Number(TypedNumber),
}

#[derive(Debug, Default)]
pub struct Expression {
  pub returns: Type,
  pub t: ExprT,
  pub span: Span,
}
impl std::fmt::Debug for ExprT {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::None => write!(f, "()"),
      Self::Func { func, this, args, send, .. } => {
        match this {
          Some(this) => f.write_str(&format!("{}{}{}@{:?}{:?}", func.ns, if *send {":"} else {"."}, func.name, this, args)),
          None => f.write_str(&format!("{}{}{}{:?}", func.ns, if *send {":"} else {"."}, func.name, args)),
        }
      }
      Self::Expr(arg0) => write!(f, "{:?}", arg0),
      Self::String(arg0) => write!(f, "{:?}", arg0),
      Self::Number(arg0) => write!(f, "{:?}", arg0),
    }
  }
}

#[derive(Debug, Default)]
pub struct Info {
  pub should: Option<Type>,
  pub expr: Expression,
  pub display: String,
  pub span: Span,
  pub expr_span: Span,
}

impl Info {
  pub fn ty(&self) -> &Type {
    return self.should.as_ref().unwrap_or(&self.expr.returns)
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
    self.infos.entry(id).or_default();
    self.found.insert(name.to_string(), id);
    self.get_info(id).display = name.to_string();
    self.get_info(id).should = Some(Type::Contract(name.to_string()));
    self.funcs.insert(name.to_string(), scope);
  }

  pub fn new_id(&mut self) -> Id {
    let id = Id(self.last_id.0+1);
    self.last_id = id;
    id
  }

  pub fn get_info(&mut self, id: Id) -> &mut Info {
    self.infos.get_mut(&id).unwrap()
  }

  pub fn find_name(&self, name: &str) -> Option<Id> {
    self.found.get(name).copied()
  }

  pub fn insert_expr(&mut self, expr: Expression) -> Id {
    let id = self.insert_name("", expr.span.clone());
    trace!("insert expr: {:?} {:?}", id, expr.t);
    self.get_info(id).expr = expr;
    id
  }

  pub fn insert_name(&mut self, name: &str, span: Span) -> Id {
    if name == "" {
      let id = self.new_id();
      self.infos.entry(id).or_default();
      self.get_info(id).display = format!("$${}", id.0);
      self.get_info(id).span = span;
      return id
    }
    if name.starts_with("$") {
      if let Some(id) = self.found.get(name).copied() {
        return id
      }
    }

    let id = self.new_id();
    self.infos.entry(id).or_default();
    self.get_info(id).display = name.to_string();
    self.get_info(id).span = span;
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
  let rhs = parse_expr(state, &stmt.rhs)?;
  let id = match &stmt.lhs {
    Some(ident) => state.insert_name(&ident.to_string(), ident.span.clone()),
    None => state.insert_name(&String::new(), stmt.span.clone())
  };
  state.get_info(id).expr_span = stmt.rhs.span.clone();
  state.get_info(id).expr = rhs;
  Ok(())
}

pub fn parse_expr(state: &mut Typing, expr: &Expr) -> Result<Expression> {
  let mut result = Expression::default();
  match &expr.expr {
    ExprKind::Ident(i) => {
      let dst = state.find_name(&i.to_string());
      match dst {
        Some(dst) => {
          result.returns = state.get_info(dst).ty().clone();
          result.t = ExprT::Expr(dst);
        },
        None => return Err(Error::NameNotFound(i.to_string(), i.span.clone()))
      }
    },
    ExprKind::Funccall(i) => {
      let (this, func) = parse_func(state, i)?;
      let args = i.args.iter().map(|t| parse_expr(state, t)).collect::<Result<Vec<_>>>()?;
      let mut arg_ids = Vec::new();
      let mut arg_types = Vec::new();
      for arg in args {
        arg_types.push(arg.returns.clone());
        if let ExprT::Expr(id) = &arg.t {
          arg_ids.push(*id);
        } else {
          arg_ids.push(state.insert_expr(arg));
        }
      }
      match func.infer_type(&arg_types) {
        Some(ty) => result.returns = ty,
        None => return Err(Error::InferTypeFailed(func.clone(), i.span.clone()))
      }
      result.t = ExprT::Func { abi: func.select(&arg_types), func, this, args: arg_ids, send: i.dot.is_send() };
    },
    ExprKind::String(i) => {
      result.returns = Type::String(i.prefix.clone().unwrap_or_default());
      result.t = ExprT::String(i.clone());
    },
    ExprKind::Number(i) => {
      result.returns = Type::Number(i.suffix.clone());
      result.t = ExprT::Number(i.clone());
    },
    _ => unreachable!(),
  };
  Ok(result)
}

fn parse_func(state: &mut Typing, i: &Funccall) -> Result<(Option<Id>, Func)> {
  let mut this = None;
  let scope = match &i.scope {
    Some(expr) => {
      let name = expr.to_string();
      if let Some(id) = state.find_name(&name) {
        this = Some(id);
        state.get_info(id).ty().clone()
      } else {
        Type::NoneType
      }
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
    Some(func) => Ok((this, func)),
    None => Err(Error::FuncNotFound(scope_str, i.name.to_string(), i.span.clone())),
  }
}
