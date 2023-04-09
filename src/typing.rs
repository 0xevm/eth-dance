use std::{collections::BTreeMap, rc::Rc, path::{Path, PathBuf}};

use crate::{
  ast::{Stmt, ExprKind, Span, StringPrefix, NumberSuffix, ExprLit, Funccall, TypedNumber, TypedString},
  abi::{Scope, Func, globals, load_abi},
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
  #[error("typing: infer type failed {0}.{1} at {1:?}")]
  InferTypeFailed(String, String, Span),
  #[error("typing: io {0:?} path={1} at {2:?}")]
  Io(#[source] std::io::Error, String, Span),
  #[error("typing: path {0:?} path={1} at {2:?}")]
  Path(#[source] std::path::StripPrefixError, String, Span),
  #[error("typing: abi {0:?} path={1} at {2:?}")]
  Abi(#[source] anyhow::Error, String, Span),
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

#[derive(Debug, Clone, Default, PartialEq)]
pub enum Type {
  #[default] NoneType,
  Global(String),
  ContractType(String),
  Contract(String),
  Function(String, String),
  Abi(ethabi::param_type::ParamType),
  String(StringPrefix), // the prefix
  Number(NumberSuffix),
}

#[derive(Debug, Default)]
pub enum ExprCode {
  #[default] None,
  Func { func: Func, this: Option<Id>, args: Vec<Id>, send: bool },
  Expr(Id),
  String(TypedString),
  Number(TypedNumber),
}

#[derive(Debug, Default)]
pub struct Expression {
  pub returns: Type,
  pub code: ExprCode,
  pub span: Span,
}
impl std::fmt::Display for ExprCode {
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
      Self::String(arg0) => write!(f, "{}", arg0),
      Self::Number(arg0) => write!(f, "{}", arg0),
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
  pub current_file: PathBuf,
  pub working_dir: PathBuf,
  pub last_id: Id,
  pub infos: BTreeMap<Id, Info>,
  pub contracts: BTreeMap<String, Scope>,
  pub found: BTreeMap<String, Id>,
}

impl Typing {
  pub fn new(current_file: PathBuf, working_dir: PathBuf) -> Self {
    let mut contracts = BTreeMap::new();
    for scope in globals() {
      contracts.insert(scope.name.to_string(), scope);
    }
    Self {
      current_file,
      working_dir,
      last_id: Id(0),
      infos: BTreeMap::new(),
      contracts,
      found: BTreeMap::new(),
    }
  }

  pub fn add_scope(&mut self, contract: Scope) -> Id {
    let id = self.new_id();
    self.infos.entry(id).or_default();
    self.found.insert(contract.name.to_string(), id);
    self.get_info(id).display = contract.name.to_string();
    self.get_info(id).should = Some(Type::ContractType(contract.name.to_string()));
    if let Some(bytecode) = &contract.bytecode {
      self.get_info(id).expr.code = ExprCode::String(TypedString { prefix: "hex".to_string(), value: bytecode.to_string().into(), span: Span::default() });
      self.get_info(id).expr.returns = Type::String("hex".to_string())
    }
    self.contracts.insert(contract.name.to_string(), contract);
    id
  }

  pub fn new_id(&mut self) -> Id {
    let id = Id(self.last_id.0+1);
    self.last_id = id;
    id
  }

  pub fn get_info(&mut self, id: Id) -> &mut Info {
    self.infos.get_mut(&id).unwrap()
  }

  pub fn get_info_view(&self, id: Id) -> &Info {
    self.infos.get(&id).unwrap()
  }

  pub fn find_name(&self, name: &str) -> Option<Id> {
    self.found.get(name).copied()
  }

  pub fn insert_expr(&mut self, expr: Expression) -> Id {
    let id = self.insert_name("", expr.span.clone());
    trace!("insert expr: {:?} {:?}", id, expr.code);
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
    Some(expr) => {
      let id = match &expr.inner {
        ExprKind::Ident(ident) => state.insert_name(&ident.to_string(), ident.span.clone()),
        _ => unreachable!("expr should must be ident"),
      };
      if !expr.hint.is_empty() {
        let hint = if expr.hint.starts_with('@') {
          expr.hint.trim_start_matches('@')
        } else { &expr.hint };
        let contract_id = state.find_name(hint);
        let contract = contract_id.map(|id| state.get_info(id).ty().clone());
        trace!("hint: {} => {:?}", expr.hint, contract);
        match contract {
          Some(Type::ContractType(s)) =>
            state.get_info(id).should = Some(Type::Contract(s)),
          _ => {
            warn!("fixme: contract not found");
          }
        }
        warn!("fixme: built-in hint {}", expr.hint);
      }
      id
    }
    None => state.insert_name(&String::new(), stmt.span.clone())
  };
  state.get_info(id).expr_span = stmt.rhs.span.clone();
  state.get_info(id).expr = rhs;
  Ok(())
}

pub fn parse_expr(state: &mut Typing, expr: &ExprLit) -> Result<Expression> {
  let span = expr.span.clone();
  let mut result = Expression::default();
  match &expr.inner {
    ExprKind::Ident(i) => {
      let dst = state.find_name(&i.to_string());
      match dst {
        Some(dst) => {
          result.returns = state.get_info(dst).ty().clone();
          result.code = ExprCode::Expr(dst);
        },
        None => return Err(Error::NameNotFound(i.to_string(), i.span.clone()))
      }
    },
    ExprKind::Funccall(i) => {
      let code = parse_func(state, i)?;
      if let ExprCode::Func { func, this, .. } = &code {
        if func.ns == "@Global" && func.name == "deploy" {
          result.returns = match state.get_info(this.unwrap()).ty() {
            Type::ContractType(i) => Type::Contract(i.to_string()),
            t => return Err(Error::ScopeNotContract(t.clone(), span.clone())),
          };
        } else {
          result.returns = func.returns();
        }
      } else {
        unreachable!()
      }
      result.code = code;
    },
    ExprKind::String(i) if i.prefix == "contract" => {
      let path = String::from_utf8(i.value.clone()).unwrap();
      let real_path = if path.starts_with(".") {
        warn!("fixme: resolve path related to work");
        Path::new(&state.current_file).parent().unwrap().join(&path).canonicalize()
      } else {
        Path::new(&state.working_dir).join(&path.strip_prefix("@/").unwrap()).canonicalize()
      }.map_err(|e| Error::Io(e, path.clone(), span.clone()))?;
      let resolved_path = format!("@/{}", real_path.strip_prefix(&state.working_dir).map_err(|e| Error::Path(e, path.clone(), span.clone()))?.to_string_lossy());
      let content = std::fs::read_to_string(real_path).map_err(|e| Error::Io(e, resolved_path.clone(), span.clone()))?;
      let scope = load_abi(&resolved_path, &content).map_err(|e| Error::Abi(e, resolved_path.clone(), span.clone()))?;
      let id = state.add_scope(scope);
      result.returns = Type::ContractType(resolved_path);
      result.code = ExprCode::Expr(id);
    },
    ExprKind::String(i) => {
      result.returns = Type::String(i.prefix.clone());
      result.code = ExprCode::String(i.clone());
    },
    ExprKind::Number(i) => {
      result.returns = Type::Number(i.suffix.clone());
      result.code = ExprCode::Number(i.clone());
    },
    _ => unreachable!(),
  };
  result.span = span;
  Ok(result)
}

fn parse_func(state: &mut Typing, i: &Funccall) -> Result<ExprCode> {
  let mut this = None;
  let scope_ty = if i.scope.to_string() != "" {
    let name = i.scope.to_string();
    if let Some(id) = state.find_name(&name) {
      this = Some(id);
      trace!("func scope: {} {:?}", name, state.get_info(id));
      state.get_info(id).ty().clone()
    } else if state.contracts.contains_key(&name) {
      Type::Global(name)
    } else {
      Type::NoneType
    }
  } else {
    Type::Global("@Global".to_string())
  };
  let scope_str = match scope_ty {
    Type::Global(name) => name.to_string(),
    Type::Contract(name) => name.clone(),
    _ => return Err(Error::ScopeNotContract(scope_ty, i.span.clone())),
  };

  let name = i.name.to_string();
  let mut args = i.args.iter().map(|t| parse_expr(state, t)).collect::<Result<Vec<_>>>()?;
  if scope_str == "@Global" && name == "deploy" {
    if args.is_empty() {
      return Err(Error::InferTypeFailed(scope_str, "deploy:this".to_string(), i.span.clone()))
    }
    this = match args.remove(0).code {
      ExprCode::Expr(i) => Some(i),
      _ => todo!()
    };
  }
  let mut arg_ids = Vec::new();
  let mut arg_types = Vec::new();
  for arg in args {
    arg_types.push(arg.returns.clone());
    arg_ids.push(state.insert_expr(arg));
  }
  let func = if scope_str == "@Global" && name == "deploy" {
    state.contracts.get(&scope_str).and_then(|i| i.funcs.get(&name)).map(|i| i[0].clone()).unwrap()
  } else {
    match state.contracts.get(&scope_str).and_then(|i| i.select(&name, &arg_types)) {
      Some(func) => func,
      None => return Err(Error::InferTypeFailed(scope_str, name, i.span.clone()))
    }
  };
  for (id, abi) in arg_ids.iter().zip(&func.input_types) {
    state.get_info(*id).should = Some(Type::Abi(abi.clone()));
  }
  Ok(ExprCode::Func { func, this, args: arg_ids, send: i.dot.is_send() })
}
