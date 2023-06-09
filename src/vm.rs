use std::collections::BTreeMap;

use anyhow::bail;
use bigdecimal::ToPrimitive;
use ethabi::{Token, ParamType};
use ethers::{
  types::{Address, TransactionRequest, TransactionReceipt},
  providers::Middleware,
  signers::{LocalWallet, Signer},
};

use crate::{
  typing::{Typing, ExprCode, CodeId, Type, Info},
  abi::Func,
};

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;

// pub struct Error {

// }
// pub type Result<T, E=Error> = std::result::Result<T, E>;
pub use anyhow::Result;

#[derive(Clone, PartialEq)]
pub enum ValueKind {
  Bool(bool),
  Number(bigdecimal::BigDecimal),
  Address(Address),
  Wallet(LocalWallet), // Custom(key)
  Receipt(TransactionReceipt),
  String(String), // String
  Bytes(Vec<u8>), // Custom(hex)
  Bytecode(Vec<u8>), // Custom(contract)
  Array(Vec<ValueKind>, Type),
  Tuple(Vec<Value>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Value {
  pub v: ValueKind,
  pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ValueKey {
  Idx(usize),
  Address(Address),
  String(String),
}

/// see also [`crate::convert::value_into`] and [`crate::convert::value_from`]
impl Value {
  pub const NONE: Value = Self { v: ValueKind::Tuple(Vec::new()), ty: Type::NoneType };
  pub fn new(v: ValueKind, ty: Type) -> Result<Self> {
    Ok(Self { v, ty })
  }
  pub fn show(&self) -> String {
    const MAX_LEN: usize = 64;
    let s = format!("{:?}", self.v);
    if s.len() > MAX_LEN {
      format!("{}...: {}", &s[..MAX_LEN/2], self.ty)
    } else {
      s
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ValueId(pub u64, pub u64);
impl ValueId {
  pub fn next_gen(self) -> Self {
    Self(self.0, self.1+1)
  }
  pub fn code(self) -> CodeId {
    CodeId(self.0)
  }
}

#[derive(Debug, Clone)]
pub struct ValueInfo {
  pub name: String,
  pub keys: Vec<(ValueId, usize)>,
}

#[derive(Debug, Default)]
pub struct BuiltIn {
  pub wallet: Option<LocalWallet>,
  pub confirm_interval: Option<f64>,
  pub force_send: bool,
}
pub struct VM {
  pub generation: BTreeMap<CodeId, ValueId>,
  pub values: BTreeMap<ValueId, Value>,
  pub infos: BTreeMap<ValueId, ValueInfo>,
  pub containers: BTreeMap<CodeId, Vec<(Vec<(ValueId, usize)>, ValueId)>>,
  pub builtin: BTreeMap<String, ValueId>,
  pub loop_idxes: Vec<(ValueId, usize)>,
  pub state: BuiltIn,
  pub provider: Provider,
}

impl VM {
  pub fn new() -> Self {
    Self {
      generation: Default::default(),
      values: Default::default(),
      infos: Default::default(),
      containers: Default::default(),
      builtin: Default::default(),
      loop_idxes: Default::default(),
      state: Default::default(),
      provider: Provider::try_from("http://localhost:8545").unwrap(),
    }
  }
  pub fn set_builtin(&mut self, name: &str, id: ValueId, value: &Value) {
    match name {
      "$endpoint" => match &value.v {
        ValueKind::String(s) => {
          *self.provider.url_mut() = url::Url::parse(s).unwrap();
        }
        _ => unreachable!()
      }
      "$account" => match &value.v {
        ValueKind::Wallet(wallet) => {
          self.state.wallet = Some(wallet.clone());
        }
        _ => unreachable!()
      }
      "$confirm_interval" => match &value.v {
        ValueKind::Number(number) => {
          self.state.confirm_interval = Some(number.to_f64().unwrap());
        }
        _ => unreachable!()
      }
      "$force_send" => match &value.v {
        ValueKind::Bool(b) => self.state.force_send = *b,
        _ => unreachable!()
      }
      _ => warn!("unknown builtin name {}", name)
    };
    self.builtin.insert(name.to_string(), id);
  }
  pub fn get_keys(&self, id: ValueId) -> Option<Vec<ValueKey>> {
    let info = self.infos.get(&id)?;
    let result = info.keys.iter().map(|(id, idx)| {
      self.values.get(id).and_then(Value::as_value_key).unwrap_or_else(|| ValueKey::Idx(*idx))
    }).collect();
    Some(result)
  }
  pub fn get_display_name(&self, id: ValueId) -> Option<String> {
    let info = self.infos.get(&id)?;
    let keys = self.get_keys(id)?;
    let mut s = if info.name.is_empty() { format!("{}", id) } else { info.name.clone() };
    for i in keys {
      s += &format!(".{}", i);
    }
    Some(s)
  }
  pub fn get_value(&self, id: CodeId) -> Option<&Value> {
    if let Some(id) = self.generation.get(&id) {
      self.values.get(id)
    } else {
      None
    }
  }
  pub fn set_value(&mut self, code_id: CodeId, info: &Info, value: Value) -> Result<ValueId> {
    let value_id = self.generation.entry(code_id).or_insert(ValueId(code_id.0, 0)).next_gen();
    self.generation.insert(code_id, value_id);
    trace!("set_value: {} {}: {} = {}", code_id, value_id, value.ty, value.show());
    // let value = try_convert(info.ty(), value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    if info.display.starts_with("$") && !info.display.starts_with("$$") {
      self.set_builtin(&info.display, value_id, &value);
    }
    self.values.insert(value_id, value);
    if let Some((ValueId(c, 0), idx)) = self.loop_idxes.last().copied() {
      if c == value_id.0 {
        *self.loop_idxes.last_mut().unwrap() = (value_id, idx);
      }
    }
    let info = ValueInfo {
      name: info.display.clone(),
      keys: self.loop_idxes.clone(),
    };
    if info.keys.len() > 0 {
      self.containers.entry(code_id).or_default().push((info.keys.clone(), value_id));
    }
    self.infos.insert(value_id, info);
    Ok(value_id)
  }
  // pub fn get_address(&self, id: Id) -> Option<Address> {
  //   match self.get_value(&id)?.token {
  //     Token::Address(addr) => Some(addr),
  //     _ => None,
  //   }
  // }
}

impl ExprCode {
  pub fn show(&self) -> String {
    const MAX_LEN: usize = 500;
    let code_str = self.to_string();
    if code_str.len() > MAX_LEN {
      code_str[..MAX_LEN].to_string() + "..."
    } else {
      code_str.to_string()
    }
  }
  pub fn show_var(&self, vm: &VM) -> String {
    const MAX_LEN: usize = 500;
    let expand = |c: &regex::Captures| -> String {
      let id = c.get(1).unwrap().as_str().parse::<CodeId>().unwrap();
      match vm.get_value(id) {
        Some(a) => a.show(),
        None => format!("~{}~", id),
      }
    };
    let re = regex::Regex::new(r"(\$\$\d+)").unwrap();
    let code_str = self.to_string();
    let code_str = re.replace_all(&code_str, expand);
    if code_str.len() > MAX_LEN {
      code_str[..MAX_LEN].to_string() + "..."
    } else {
      code_str.to_string()
    }
  }
}

pub fn execute(vm: &mut VM, typing: &Typing, start: Option<CodeId>, end: Option<CodeId>) -> Result<()> {
  let mut skipping = CodeId(0);
  info!("execute: {:?} {:?}", start, end);
  let code_range = typing.infos.iter()
    .skip_while(|(id, _)| start.is_some() && **id <= start.unwrap()) // <= means exclude start
    .take_while(|(id, _)| end.is_none() || **id < end.unwrap()); // < means exlude end
  for (id, info) in code_range {
    if *id < skipping { continue }
    debug!("code: {} <- {}", id, info.expr.code.show_var(vm));
    let value = match &info.expr.code {
      ExprCode::None => {
        warn!("expr is none: {:?}", id);
        continue
      },
      ExprCode::Loop(scope, stop) => {
        skipping = *stop;
        let Some(range) = vm.get_value(*scope).cloned() else {
          bail!("scope range {} not present", scope);
        };
        vm.loop_idxes.push((ValueId(id.0, 0), 0));
        match range.v {
          ValueKind::Array(arr, ty) => {
            for (idx, item) in arr.into_iter().enumerate() {
              *vm.loop_idxes.last_mut().unwrap() = (ValueId(id.0, 0), idx+1);
              vm.set_value(*id, info, Value::new(item, ty.clone())?)?;
              execute(vm, typing, Some(*id), Some(*stop))?;
            }
          }
          _ => bail!("scope range {} not iteratable: {}", scope, range.ty),
        }
        vm.loop_idxes.pop();
        continue
      }
      ExprCode::EndLoop(_) => {
        continue
      }
      _ => execute_impl(vm, typing, &info.expr.code, Some(&info.ty()))?,
    };
    vm.set_value(*id, info, value)?;
  }
  Ok(())
}

fn execute_impl(vm: &mut VM, typing: &Typing, code: &ExprCode, ty: Option<&Type>) -> Result<Value> {
  let value = match &code {
    ExprCode::None | ExprCode::Loop(_, _) | ExprCode::EndLoop(_) => {
      warn!("skip {:?}: {:?}", ty, code);
      Value::NONE
    }
    ExprCode::Convert(i, ty) => {
      let value = if let Some(value) = vm.get_value(*i) {
        value.clone()
      } else {
        anyhow::bail!("vm: copy value from {:?} failed", i);
      };
      match ty {
        Some(ty) => match value.as_ty(ty) {
          Ok(i) | Err(i) => i
        }
        None => value,
      }
    }
    ExprCode::Func { func, this, args, send } => {
      let args = args.iter().map(|i| vm.get_value(*i)).collect::<Option<Vec<_>>>().ok_or_else(|| anyhow::format_err!("vm: args no present"))?;
      if func.name == "constructor" && *send {
        let this = this.unwrap();
        trace!("contract name {}", &func.ns);
        let Some(bytecode) = vm.get_value(this).and_then(Value::as_bytecode) else {
          anyhow::bail!("vm: contract bytecode not present")
        };
        let result = deploy_contract(vm, func.clone(), bytecode, &args)?;
        Value::from_receipt(result)
      } else if !func.ns.0.starts_with("@/") {
        call_global(vm, func.clone(), &args)?
      } else if let Some(this) = this {
        let Some(this_addr) = vm.get_value(*this).and_then(Value::as_address) else {
          anyhow::bail!("vm: this not address {} = {:?}", this, vm.get_value(*this))
        };
        trace!("this_addr: {:?} {:?}", this, this_addr);
        if *send {
          let receipt = send_tx(vm, this_addr, func.clone(), &args)?;
          Value::from_receipt(receipt)
        } else {
          call_tx(vm, this_addr, func.clone(), &args, ty)?
        }
      } else {
        unreachable!()
      }
    }
    ExprCode::Number(number) => {
      Value::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?
    }
    ExprCode::String(string) => {
      Value::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?
    }
    ExprCode::Const(value) => {
      value.clone()
    }
    ExprCode::List(list) => {
      let mut values = Vec::new();
      let mut sub_ty = None;
      for i in list {
        let value = execute_impl(vm, typing, i, sub_ty.as_ref())?;
        if let Some(sub_ty) = &sub_ty {
          if &value.ty != sub_ty {
            error!("execute array sub_ty: {} != {}", sub_ty, value.ty);
          }
        } else {
          sub_ty = Some(value.ty)
        }
        values.push(value.v)
      }
      let sub_ty = sub_ty.unwrap_or_default();
      Value::new(ValueKind::Array(values, sub_ty.clone()), Type::FixedArray(Box::new(sub_ty), list.len()))?
    },
    ExprCode::Access(container_id, arg_ids) => {
      let Some(container) = vm.containers.get(container_id) else {
        anyhow::bail!("id not container: {}", container_id);
      };
      let Some(args) = arg_ids.iter().map(|i| vm.get_value(*i)).collect::<Option<Vec<_>>>() else {
        anyhow::bail!("some args not found: {:?}", arg_ids);
      };
      let arg_idx = args.iter().map(|i| i.as_number().and_then(|i| i.0.to_u64())).collect::<Vec<_>>();
      let args = args.iter().map(|i| i.as_value_key()).collect::<Vec<_>>();
      let mut result = None;
      trace!("access {} {} with {:?} and {:?}", container_id, container.len(), arg_idx, args);
      for k in container {
        let Some(args2) = k.0.iter().map(|i| vm.values.get(&i.0)).collect::<Option<Vec<_>>>() else {
          anyhow::bail!("some args (container) not found: {:?}", k.0);
        };
        let args2 = args2.iter().map(|i| i.as_value_key()).collect::<Vec<_>>();
        trace!("access {} with {:?} and {:?}", container_id, &k.0, args2);
        if args.iter().zip(&arg_idx).zip(args2.iter().zip(&k.0)).all(|((i1, i2), (j1, (_, j2)))| {
          (i1.is_some() && i1 == j1) || i2 == &Some(*j2 as _)
        }) {
          result = Some(k.1);
        }
      }
      vm.values.get(&result.unwrap()).unwrap().clone()
    }
  };
  Ok(match ty {
    Some(ty) => match value.as_ty(ty) {
      Ok(i) | Err(i) => i
    }
    None => value,
  })
}

fn call_global(_vm: &VM, func: Func, args: &[&Value]) -> Result<Value> {
  let out = match (func.ns.0.as_str(), func.name.as_str()) {
    ("@assert", "eq") => {
      if args[0] != args[1] {
        anyhow::bail!("vm: assert_eq failed: {:?} != {:?}", args[0], args[1])
      }
      Value::from_bool(true)
    }
    _ => unreachable!()
  };
  Ok(out)
}

#[tokio::main]
async fn do_send_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<TransactionReceipt> {
  if let Some(wallet) = &vm.state.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  let pending = match vm.provider.send_transaction(tx.clone(), None).await {
    Ok(pending) => pending,
    Err(_) if vm.state.force_send => {
      vm.provider.send_transaction(tx.gas(200_000), None).await?
    }
    e => e?,
  };
  let tx_hash = pending.tx_hash();
  trace!("pending: {:?}", pending);
  let pending = if let Some(i) = vm.state.confirm_interval {
    pending.interval(std::time::Duration::from_secs_f64(i))
  } else {
    pending
  };
  Ok(pending.await?.ok_or_else(|| anyhow::anyhow!("transaction not found: {}", tx_hash))?)
}

#[tokio::main]
async fn do_call_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<ethabi::Bytes> {
  if let Some(wallet) = &vm.state.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  Ok(vm.provider.call(&tx.into(), None).await?.to_vec())
}

fn convert_to_token(input_types: &[ParamType], args: &[&Value]) -> Result<Vec<Token>> {
  let result = args.iter().zip(input_types).map(|(i, abi)| i.clone().into_token(abi)).collect::<Result<_, _>>()?;
  Ok(result)
}
fn convert_from_token(ty: Option<&Type>, mut args: Vec<Token>) -> Result<Value> {
  let arg = if args.len() == 1 {
    args.remove(0)
  } else {
    Token::Tuple(args)
  };
  Ok(Value::from_token_ty(arg, ty)?)
}

fn send_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value]) -> Result<TransactionReceipt> {
  info!("send_tx: {} {}.{}({})", this_addr, func.ns, func.name, args.iter().map(|i| i.show()).collect::<Vec<_>>().join(", "));
  let tokens = convert_to_token(&func.input_types, args)?;
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let result = do_send_tx_sync(vm, tx)?;
  if result.status.map(|i| i.as_u64()) != Some(1) {
    error!("reverted: {:?}", result);
    return Err(anyhow::anyhow!("reverted: {:?}", result))
  }
  Ok(result)
}

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value], ty: Option<&Type>) -> Result<Value> {
  let tokens = convert_to_token(&func.input_types, args)?;
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("call_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let bytes = do_call_tx_sync(vm, tx)?;
  let out = ethabi::decode(&func.output_types, &bytes)?;
  let result = convert_from_token(ty, out)?;
  // vm.provider.
  Ok(result)
}

fn deploy_contract(vm: &VM, func: Func, bytecode: &[u8], args: &[&Value]) -> Result<TransactionReceipt> {
  let tokens = convert_to_token(&func.input_types, args)?;
  info!("deploy_contract: {} {} to {}", func.ns, bytecode.len(), vm.provider.url());
  let mut input_data = Vec::new();
  input_data.extend_from_slice(bytecode);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  let tx = TransactionRequest::new().data(input_data);//.from(vm.builtin.account);
  let receipt = do_send_tx_sync(vm, tx)?;
  Ok(receipt)
}
