use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast::{TypeLit, TypeKind, TypePrefix, StmtKind, Forloop};
use crate::{
  ast::{Assignment, ExprKind, Span, StringPrefix, NumberSuffix, ExprLit, Funccall, TypedNumber, TypedString},
  abi::{Module, Func, globals, load_abi},
};

#[derive(Debug, thiserror::Error)]
pub enum Error {
  #[error("typing: {0:?}")]
  Errors(Vec<Error>),
  #[error("typing: name not found {0:?} at {1:?}")]
  NameNotFound(String, Span),
  #[error("typing: module not contract {0:?} at {1:?}")]
  ModuleNotContract(Type, Span),
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
  #[error("typing: abi_type {0:?} at {1:?}")]
  AbiType(#[source] ethabi::Error, Span),
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
      Error::ModuleNotContract(_, span) |
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
  Expr(Id),
  String(TypedString),
  Number(TypedNumber),
  List(Vec<ExprCode>),
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
}

impl Info {
  pub fn ty(&self) -> &Type {
    return self.should.as_ref().unwrap_or(&self.expr.returns)
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Id(pub u64, pub u64);
pub struct Typing {
  pub current_file: PathBuf,
  pub working_dir: PathBuf,
  pub last_id: Id,
  pub infos: BTreeMap<Id, Info>,
  pub modules: BTreeMap<String, Module>,
  pub found: BTreeMap<String, Id>,
}

impl Typing {
  pub fn new(current_file: PathBuf, working_dir: PathBuf) -> Self {
    let mut contracts = BTreeMap::new();
    for module in globals() {
      contracts.insert(module.name.to_string(), module);
    }
    Self {
      current_file,
      working_dir,
      last_id: Id(0, 0),
      infos: BTreeMap::new(),
      modules: contracts,
      found: BTreeMap::new(),
    }
  }

  pub fn add_module(&mut self, contract: Module) -> Id {
    let id = self.new_id();
    self.infos.entry(id).or_default();
    self.found.insert(contract.name.to_string(), id);
    self.get_info(id).display = contract.name.to_string();
    self.get_info(id).should = Some(Type::ContractType(contract.name.to_string()));
    if let Some(bytecode) = &contract.bytecode {
      self.get_info(id).expr.code = ExprCode::String(TypedString { prefix: StringPrefix::Bytecode, value: bytecode.to_string().into(), span: Span::default() });
      self.get_info(id).expr.returns = Type::String(StringPrefix::Bytecode)
    }
    self.modules.insert(contract.name.to_string(), contract);
    id
  }

  pub fn new_id(&mut self) -> Id {
    let id = Id(self.last_id.0+1, 0);
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
    // if name.starts_with("$") {
    //   if let Some(id) = self.found.get(name).copied() {
    //     return id
    //   }
    // }

    let id = self.new_id();
    self.infos.entry(id).or_default();
    self.get_info(id).display = name.to_string();
    self.get_info(id).span = span;
    self.found.insert(name.to_string(), id);
    id
  }
}

pub fn parse_file(state: &mut Typing, stmts: &[StmtKind]) -> Result<()> {
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
pub fn parse_stmt(state: &mut Typing, stmt: &StmtKind) -> Result<()> {
  match stmt {
    StmtKind::Assignment(stmt) => parse_assignment(state, stmt),
    StmtKind::Forloop(stmt) => parse_forloop(state, stmt),
    StmtKind::Comment(_) => Ok(()),
  }
}

fn parse_forloop(state: &mut Typing, stmt: &Forloop) -> Result<()> {
  let rhs = parse_expr(state, &stmt.rhs)?;
  Ok(())
}

pub fn parse_assignment(state: &mut Typing, stmt: &Assignment) -> Result<()> {
  let rhs = parse_expr(state, &stmt.rhs)?;
  let id = match &stmt.lhs {
    Some(expr) => {
      let id = match &expr.inner {
        ExprKind::Ident(ident) => state.insert_name(&ident.to_string(), ident.span.clone()),
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
    None => state.insert_name(&String::new(), stmt.span.clone())
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
          let suffix = suffix.parse().map_err(|_| Error::NameNotFound(suffix.to_string(), hint.span.clone()))?;
          Type::Number(suffix)
        },
        _ => return Err(Error::NameNotFound(s.to_string(), hint.span.clone())),
      }
    },
    TypeKind::String(s, prefix) => {
      match prefix {
        TypePrefix::None => Type::Contract(s.to_string()),
        TypePrefix::Contract => Type::ContractType(s.to_string()),
        TypePrefix::Abi => {
          Type::Abi(ethabi::param_type::Reader::read(&s).map_err(|e| Error::AbiType(e, hint.span.clone()))?)
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
      let path = String::from_utf8(i.value.clone()).unwrap();
      let real_path = if path.starts_with(".") {
        warn!("fixme: resolve path related to work");
        Path::new(&state.current_file).parent().unwrap().join(&path).canonicalize()
      } else {
        Path::new(&state.working_dir).join(&path.strip_prefix("@/").unwrap()).canonicalize()
      }.map_err(|e| Error::Io(e, path.clone(), span.clone()))?;
      let resolved_path = format!("@/{}", real_path.strip_prefix(&state.working_dir).map_err(|e| Error::Path(e, path.clone(), span.clone()))?.to_string_lossy());
      let content = std::fs::read_to_string(real_path).map_err(|e| Error::Io(e, resolved_path.clone(), span.clone()))?;
      let module = load_abi(&resolved_path, &content).map_err(|e| Error::Abi(e, resolved_path.clone(), span.clone()))?;
      let id = state.add_module(module);
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
                codes.push(ExprCode::Expr(id))
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
    } else if state.modules.contains_key(&name) {
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
    _ => return Err(Error::ModuleNotContract(module_ty, i.span.clone())),
  };

  let name = i.name.to_string();
  let mut args = i.args.iter().map(|t| parse_expr(state, t)).collect::<Result<Vec<_>>>()?;
  let (module_str, name) = if module_str == "@Global" && name == "deploy" {
    if args.is_empty() {
      return Err(Error::InferTypeFailed(module_str, "deploy:this".to_string(), i.span.clone()))
    }
    let this_arg = args.remove(0);
    this = match this_arg.code {
      ExprCode::Expr(i) => Some(i),
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
    None => return Err(Error::InferTypeFailed(module_str, name, i.span.clone()))
  };
  for (id, abi) in arg_ids.iter().zip(&func.input_types) {
    state.get_info(*id).should = Some(Type::Abi(abi.clone()));
  }
  Ok(ExprCode::Func { func, this, args: arg_ids, send: i.dot.is_send() })
}
