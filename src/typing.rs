use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast::{TypeLit, TypeKind, TypePrefix, StmtKind, Forloop};
use crate::{
  ast::{Assignment, ExprKind, Span, StringPrefix, NumberSuffix, ExprLit, Funccall, TypedNumber, TypedString},
  abi::{Module, Func, globals, load_abi},
};

#[derive(Debug, thiserror::Error)]
pub enum ErrorKind {
  #[error(transparent)]
  Utf8(#[from] std::string::FromUtf8Error),
  #[error(transparent)]
  Io(#[from] std::io::Error),
  #[error(transparent)]
  Path(#[from] std::path::StripPrefixError),
  #[error("abi loading")]
  Abi(#[source] anyhow::Error),
  #[error(transparent)]
  AbiType(#[from] ethabi::Error),
  #[error("name not found {0:?}")]
  NameNotFound(String),
  #[error("module not contract {0:?}")]
  ModuleNotContract(Type),
  #[error("func not found {0}.{1}")]
  FuncNotFound(String, String),
  #[error("infer type failed {0}.{1}")]
  InferTypeFailed(String, String),
  #[error("loop: {0}")]
  Loop(String),
}
#[derive(Debug, thiserror::Error)]
#[error("typing: {message} at {span:?}")]
pub struct Error {
  #[source]
  pub kind: ErrorKind,
  pub message: String,
  pub span: Span,
}
pub type Result<T, E=Error> = std::result::Result<T, E>;

impl Error {
  pub fn show_pos(&self, input: &str, line_index: Rc<Vec<usize>>) -> String {
    let mut s = String::new();
    let span = &self.span;
    if span.len > 0 {
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


impl ErrorKind {
  fn when(self, span: &Span) -> Error {
    Error {
      kind: self, message: String::new(), span: span.clone(),
      // backtrace: Backtrace::force_capture(),
    }
  }
  fn context<S: ToString>(self, s: S, span: &Span) -> Error {
    Error {
      kind: self, message: s.to_string(), span: span.clone(),
      // backtrace: Backtrace::force_capture(),
    }
  }
}

pub trait ErrorExt<T, E> {
  fn when(self, span: &Span) -> Result<T>;
  fn context<S: ToString>(self, s: S, span: &Span) -> Result<T>;
}
impl<T, E: Into<ErrorKind>> ErrorExt<T, E> for Result<T, E> {
  fn when(self, span: &Span) -> Result<T> {
    self.map_err(|e| e.into().when(span))
  }
  fn context<S: ToString>(self, s: S, span: &Span) -> Result<T> {
    self.map_err(|e| e.into().context(s, span))
  }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub enum Type {
  #[default] NoneType,
  Global(String),
  ContractType(String),
  Contract(String),
  // Function(String, String),
  Abi(ethabi::ParamType),
  Bool,
  String(StringPrefix), // the prefix
  Number(NumberSuffix),
  FixedArray(Box<Type>, usize),
}

impl Type {
  pub fn abi(&self) -> Option<ethabi::ParamType> {
    Some(match self {
      Type::NoneType => ethabi::ParamType::FixedBytes(0),
      Type::Global(_) => return None,
      Type::ContractType(_) => ethabi::ParamType::Bytes,
      Type::Contract(_) => ethabi::ParamType::Address,
      // Type::Function(_, _) => return None,
      Type::Abi(i) => i.clone(),
      Type::Bool => ethabi::ParamType::Bool,
      Type::String(s) => match s {
        StringPrefix::None => ethabi::ParamType::String,
        StringPrefix::Address => ethabi::ParamType::Address,
        StringPrefix::Byte | StringPrefix::Bytecode | StringPrefix::Key | StringPrefix::Hex => ethabi::ParamType::Bytes,
        StringPrefix::Contract => todo!(),
        // _ => {
        //   unreachable!("fixme: type(string) abi {}", s)
        // }
      },
      Type::Number(i) => match i {
        NumberSuffix::F(size) => ethabi::ParamType::FixedBytes(*size / 8),
        _ if i.is_unsigned() => ethabi::ParamType::Uint(256),
        _ => ethabi::ParamType::Int(256),
      },
      Type::FixedArray(i, n) => {
        ethabi::ParamType::FixedArray(Box::new(i.abi()?), *n)
      }
    })
  }
}

#[derive(Debug, Default)]
pub enum ExprCode {
  #[default] None,
  Func { func: Func, this: Option<Id>, args: Vec<Id>, send: bool },
  Convert(Id, Option<Type>),
  String(TypedString),
  Number(TypedNumber),
  List(Vec<ExprCode>),
  Loop(Id, Id),
  EndLoop(Id),
}

#[derive(Debug, Default)]
pub struct Expression {
  pub returns: Type,
  pub code: ExprCode,
  pub span: Span,
}

#[derive(Debug, Default)]
pub struct Info {
  pub should: Option<Type>,
  pub expr: Expression,
  pub display: String,
  pub span: Span,
  pub expr_span: Span,
  pub keys: Vec<Id>,
}

impl Info {
  pub fn ty(&self) -> &Type {
    return self.should.as_ref().unwrap_or(&self.expr.returns)
  }
}

// You could not shallow names in different scope
#[derive(Debug, Clone)]
pub struct Scopes {
  pub stack: Vec<Id>,
  pub scopes: BTreeMap<Id, BTreeMap<String, Id>>,
  pub symbols: BTreeMap<String, (Id, Id)>,
  pub latest: BTreeMap<String, Id>,
}

impl Scopes {
  pub fn new() -> Self {
    let init = Id(0, 0);
    let mut scopes = BTreeMap::new();
    scopes.insert(init, Default::default());
    Self {
      stack: vec![init], scopes, symbols: Default::default(), latest: Default::default(),
    }
  }
  pub fn insert(&mut self, name: String, id: Id) -> Result<(), ErrorKind> {
    let current = *self.stack.last().unwrap();
    let current_scope = self.scopes.get_mut(&current).unwrap();
    current_scope.insert(name.to_string(), id);
    self.symbols.entry(name.to_string()).or_insert((current, id));
    self.latest.insert(name.to_string(), id);
    Ok(())
  }
  pub fn enter_scope(&mut self, id: Id) {
    self.scopes.insert(id, Default::default());
    self.stack.push(id);
  }
  pub fn exit_scope(&mut self) {
    self.stack.pop();
  }
}

#[derive(Default)]
pub struct Modules {
  pub modules: BTreeMap<ModuleName, Module>,
  pub contracts: BTreeMap<String, ModuleName>,
  pub contract_names: BTreeMap<ModuleName, String>,
}

impl Modules {
  pub fn new(predefined: Vec<Module>) -> Self {
    let mut modules = Self::default();
    for module in predefined {
      modules.insert(module);
    }
    modules
  }

  pub fn insert(&mut self, module: Module) {
    // let module_name = module.name.to_string();
    self.modules.insert(module.name.to_string(), module);
    // self.contracts.insert(name.to_string(), module_name.to_string());
    // self.contract_names.insert(module_name.to_string(), name);
  }
  pub fn get(&self, name: &str) -> Option<&Module> {
    self.modules.get(name)
  }
  pub fn contains(&self, name: &str) -> bool {
    self.modules.contains_key(name)
  }
}

pub type ModuleName = String;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id(pub u64, pub u64);
pub struct Typing {
  pub current_file: PathBuf,
  pub working_dir: PathBuf,
  pub last_id: Id,
  pub infos: BTreeMap<Id, Info>,
  pub scopes: Scopes,
  pub modules: Modules,
}

impl Typing {
  pub fn new(current_file: PathBuf, working_dir: PathBuf) -> Self {
    Self {
      current_file,
      working_dir,
      last_id: Id(0, 0),
      infos: BTreeMap::new(),
      modules: Modules::new(globals()),
      scopes: Scopes::new(),
    }
  }

  pub fn add_module(&mut self, contract: Module, span: &Span) -> Id {
    let id = self.new_id(span);
    self.infos.entry(id).or_default();
    // self.scopes.insert(contract.name.to_string(), id);
    // self.get_info(id).display = name.to_string();
    self.get_info(id).should = Some(Type::ContractType(contract.name.to_string()));
    if let Some(bytecode) = &contract.bytecode {
      self.get_info(id).expr.code = ExprCode::String(TypedString { prefix: StringPrefix::Bytecode, value: bytecode.to_string().into(), span: Span::default() });
      self.get_info(id).expr.returns = Type::String(StringPrefix::Bytecode)
    }
    self.modules.insert(contract);
    id
  }

  pub fn new_id(&mut self, span: &Span) -> Id {
    let id = Id(self.last_id.0+1, 0);
    self.infos.entry(id).or_default();
    self.get_info(id).span = span.clone();
    self.get_info(id).keys = self.scopes.stack.clone();
    self.last_id = id;
    id
  }

  pub fn get_info(&mut self, id: Id) -> &mut Info {
    self.infos.get_mut(&id).unwrap()
  }

  pub fn get_info_view(&self, id: Id) -> &Info {
    self.infos.get(&Id(id.0, 0)).unwrap()
  }

  pub fn find_name(&self, name: &str) -> Option<Id> {
    self.scopes.latest.get(name).copied()
  }

  pub fn insert_expr(&mut self, expr: Expression) -> Id {
    let id = self.new_id(&expr.span);
    trace!("insert expr: {:?} {:?}", id, expr.code);
    self.get_info(id).expr = expr;
    id
  }

  pub fn insert_name(&mut self, name: &str, span: &Span) -> Result<Id, Error> {
    let id = self.new_id(span);
    if name == "" {
      return Ok(id)
    }
    self.get_info(id).display = name.to_string();
    self.scopes.insert(name.to_string(), id).when(span)?;
    Ok(id)
  }
}

pub fn parse_file(state: &mut Typing, stmts: &[StmtKind]) -> Result<(), Vec<Error>> {
  let mut errors = Vec::new();

  let mut visited = BTreeSet::new();

  // first pass: parse modules and fn defines
  for (i, stmt) in stmts.iter().enumerate() {
    match parse_stmt_types(state, stmt) {
      Ok(true) => { visited.insert(i); }
      Err(e) => { errors.push(e); }
      _ => {},
    }
  }

  for (i, stmt) in stmts.iter().enumerate() {
    if visited.contains(&i) { continue }
    if let Err(e) = parse_stmt(state, stmt) {
      errors.push(e)
    }
  }
  if errors.is_empty() {
    Ok(())
  } else {
    Err(errors)
  }
}
pub fn parse_stmt_types(state: &mut Typing, stmt: &StmtKind) -> Result<bool> {
  match stmt {
    StmtKind::Assignment(stmt) => {
      let (ty, id) = match &stmt.rhs.inner {
        ExprKind::String(i) if i.prefix == StringPrefix::Contract =>{
          let span = &i.span;
          let path = String::from_utf8(i.value.clone()).when(&span)?;
          let real_path = if path.starts_with(".") {
            warn!("fixme: resolve path related to work");
            Path::new(&state.current_file).parent().unwrap().join(&path).canonicalize()
          } else {
            Path::new(&state.working_dir).join(&path.strip_prefix("@/").unwrap()).canonicalize()
          }.context(&path, &span)?;
          let resolved_path = format!("@/{}", real_path.strip_prefix(&state.working_dir).context(&path, &span)?.to_string_lossy());
          warn!("fixme: check resolved path in moduels {}", resolved_path);
          let content = std::fs::read_to_string(real_path).context(&resolved_path, &span)?;
          let module = load_abi(&resolved_path, &content).map_err(ErrorKind::Abi).context(&resolved_path, &span)?;
          let id = state.add_module(module, &stmt.rhs.span);
          (Type::ContractType(resolved_path), id)
        }
        _ => return Ok(false)
      };
      if let Some(lhs) = &stmt.lhs {
        let name = match &lhs.inner {
          ExprKind::Ident(i) => i.to_string(),
          _ => unreachable!("lhs must be ident"),
        };
        state.get_info(id).should = Some(ty);
        state.get_info(id).display = name.to_string();
        state.scopes.insert(name, id).when(&lhs.span)?;
      }
      Ok(true)
    }
    StmtKind::Forloop(Forloop { stmts, .. }) => {
      for i in stmts {
        parse_stmt_types(state, i)?;
      };
      Ok(false)
    }
    StmtKind::Comment(_) => Ok(true),
  }
}
pub fn parse_stmt(state: &mut Typing, stmt: &StmtKind) -> Result<()> {
  match stmt {
    StmtKind::Assignment(stmt) => parse_assignment(state, stmt),
    StmtKind::Forloop(stmt) => {
      let old_stack = state.scopes.stack.clone();
      let result = parse_forloop(state, stmt);
      state.scopes.stack = old_stack;
      result
    }
    StmtKind::Comment(_) => Ok(()),
  }
}

/// forloop would generate ir like this:
/// $$1 next(collection_id)
/// $$... stmts
/// $$3 end
fn parse_forloop(state: &mut Typing, stmt: &Forloop) -> Result<()> {
  let rhs = parse_expr(state, &stmt.rhs)?;
  let item_ty = match &rhs.returns {
    Type::FixedArray(ty, _) => ty.as_ref().clone(),
    _ => return Err(ErrorKind::Loop(format!("rhs.returns not a iterator {}", rhs.returns)).when(&stmt.span)),
  };
  let range_id = state.insert_expr(rhs);
  let name = match &stmt.lhs.inner {
    ExprKind::Ident(i) => i.to_string(),
    _ => unreachable!(),
  };
  state.scopes.enter_scope(range_id);
  let loop_id = state.insert_name(&name, &stmt.lhs.span)?;
  for i in &stmt.stmts {
    parse_stmt(state, i)?;
  }
  let end_id = state.new_id(&stmt.span);
  state.get_info(loop_id).expr = Expression {
    returns: item_ty,
    code: ExprCode::Loop(range_id, end_id),
    span: stmt.span.clone(),
  };
  state.get_info(end_id).expr = Expression {
    returns: Type::NoneType,
    code: ExprCode::EndLoop(loop_id),
    span: stmt.span.clone(),
  };
  state.scopes.exit_scope(); // TODO: ensure exit?
  Ok(())
}

pub fn parse_assignment(state: &mut Typing, stmt: &Assignment) -> Result<()> {
  let rhs = parse_expr(state, &stmt.rhs)?;
  let id = match &stmt.lhs {
    Some(expr) => {
      let id = match &expr.inner {
        ExprKind::Ident(ident) => state.insert_name(&ident.to_string(), &ident.span)?,
        _ => unreachable!("expr should must be ident"),
      };
      if let Some(hint) = &expr.hint {
        let hint = parse_type(hint)?;
        match &hint {
          Type::ContractType(s) => {
            let contract_id = state.find_name(&s);
            let contract = contract_id.map(|id| state.get_info(id).ty().clone());
            trace!("hint: {} => {:?}", hint, contract);
            match contract {
              Some(Type::ContractType(s)) =>
                state.get_info(id).should = Some(Type::Contract(s)),
              _ => {
                todo!("fixme: contract not found");
              }
            }
          }
          _ => state.get_info(id).should = Some(hint),
        }
      }
      id
    }
    None => state.new_id(&stmt.span)
  };
  state.get_info(id).expr_span = stmt.rhs.span.clone();
  state.get_info(id).expr = rhs;
  Ok(())
}

pub fn parse_type(hint: &TypeLit) -> Result<Type> {
  let ty = match &hint.kind {
    TypeKind::None => Type::NoneType,
    TypeKind::Ident(s) => {
      match s.as_str() {
        "none" => Type::NoneType,
        "bool" => Type::Bool,
        "string" => Type::String(StringPrefix::None),
        "address" => Type::String(StringPrefix::Address),
        "wallet" => Type::String(StringPrefix::Key),
        "bytes" => Type::String(StringPrefix::Byte),
        "bytecode" => Type::String(StringPrefix::Bytecode),
        _ if s.starts_with("@") => Type::Global(s[1..].to_string()),
        _ if s.starts_with("int_") => {
          let suffix = &s["int_".len()..];
          let suffix = suffix.parse().map_err(|_| ErrorKind::NameNotFound(suffix.to_string())).when(&hint.span)?;
          Type::Number(suffix)
        },
        _ => return Err(ErrorKind::NameNotFound(s.to_string()).when(&hint.span)),
      }
    },
    TypeKind::String(s, prefix) => {
      match prefix {
        TypePrefix::None => Type::Contract(s.to_string()),
        TypePrefix::Contract => Type::ContractType(s.to_string()),
        TypePrefix::Abi => {
          Type::Abi(ethabi::param_type::Reader::read(&s).when(&hint.span)?)
        },
    }
    },
    TypeKind::Array(ty, size) => {
      let inner = parse_type(&ty)?;
      Type::FixedArray(Box::new(inner), size.unwrap())
    },
};
  Ok(ty)
}

pub fn parse_expr(state: &mut Typing, expr: &ExprLit) -> Result<Expression> {
  let span = expr.span.clone();
  let mut result = Expression::default();
  let hint_ty = match &expr.hint {
    Some(hint) => Some(parse_type(hint)?),
    None => None,
  };
  match &expr.inner {
    ExprKind::Ident(i) => {
      match state.find_name(&i.to_string()) {
        Some(dst) => {
          result.returns = state.get_info(dst).ty().clone();
          result.code = ExprCode::Convert(dst, hint_ty);
        },
        None => return Err(ErrorKind::NameNotFound(i.to_string()).when(&span))
      }
    },
    ExprKind::Funccall(i) => {
      let code = parse_func(state, i)?;
      if let ExprCode::Func { func, .. } = &code {
        result.returns = if func.name == "constructor" {
          Type::Contract(func.ns.clone())
        } else {
          func.returns()
        }
      } else {
        unreachable!()
      }
      result.code = code;
    },
    ExprKind::String(i) if i.prefix == StringPrefix::Contract => {
      unreachable!()
    },
    ExprKind::String(i) => {
      result.returns = Type::String(i.prefix.clone());
      result.code = ExprCode::String(i.clone());
    },
    ExprKind::Number(i) => {
      result.returns = Type::Number(i.suffix.clone());
      result.code = ExprCode::Number(i.clone());
    },
    ExprKind::List(list) => {
      match list.kind {
        crate::ast::ExprListKind::Raw => unreachable!(),
        crate::ast::ExprListKind::FixedArray => {
          let mut codes = Vec::new();
          let mut ty = None;
          for i in &list.exprs {
            let inner = parse_expr(state, i)?;
            if let Some(ty) = &ty {
              if ty != &inner.returns {
                error!("array type: {} != {}", ty, inner.returns);
                // todo!()
              }
            } else {
              ty = Some(inner.returns.clone());
            }
            match inner.code {
              ExprCode::Func { .. } => {
                let id = state.insert_expr(inner);
                codes.push(ExprCode::Convert(id, ty.clone()))
              },
              _ => codes.push(inner.code),
            }
            ;
          }
          result.returns = Type::FixedArray(Box::new(ty.unwrap_or_default()), codes.len());
          result.code = ExprCode::List(codes);
        }
      }
    },
    _ => unreachable!(),
  };
  result.span = span;
  Ok(result)
}

fn parse_func(state: &mut Typing, i: &Funccall) -> Result<ExprCode> {
  let mut this = None;
  let module_ty = if i.module.to_string() != "" {
    let name = i.module.to_string();
    if let Some(id) = state.find_name(&name) {
      this = Some(id);
      trace!("func module: {} {:?}", name, state.get_info(id));
      state.get_info(id).ty().clone()
    } else if state.modules.contains(&name) {
      Type::Global(name)
    } else {
      Type::NoneType
    }
  } else {
    Type::Global("@Global".to_string())
  };
  let module_str = match module_ty {
    Type::Global(name) => name.to_string(),
    Type::Contract(name) => name.clone(),
    _ => return Err(ErrorKind::ModuleNotContract(module_ty).when(&i.span)),
  };

  let name = i.name.to_string();
  let mut args = i.args.iter().map(|t| parse_expr(state, t)).collect::<Result<Vec<_>>>()?;
  let (module_str, name) = if module_str == "@Global" && name == "deploy" {
    if args.is_empty() {
      return Err(ErrorKind::InferTypeFailed(module_str, "deploy:this".to_string()).when(&i.span.clone()))
    }
    let this_arg = args.remove(0);
    this = match this_arg.code {
      ExprCode::Convert(i, _) => Some(i),
      _ => todo!(),
    };
    let module_str = match this_arg.returns {
      Type::ContractType(i) => i,
      _ => todo!(),
    };
    trace!("deploy: this = {:?} {}", this, module_str);
    (module_str, "constructor".to_string())
  } else {
    (module_str, name)
  };
  let mut arg_ids = Vec::new();
  let mut arg_types = Vec::new();
  for arg in args {
    arg_types.push(arg.returns.clone());
    arg_ids.push(state.insert_expr(arg));
  }
  let func = match state.modules.get(&module_str).and_then(|i| i.select(&name, &arg_types)) {
    Some(func) => func,
    None => return Err(ErrorKind::InferTypeFailed(module_str, name).when(&i.span))
  };
  for (id, abi) in arg_ids.iter().zip(&func.input_types) {
    state.get_info(*id).should = Some(Type::Abi(abi.clone()));
  }
  Ok(ExprCode::Func { func, this, args: arg_ids, send: i.dot.is_send() })
}
