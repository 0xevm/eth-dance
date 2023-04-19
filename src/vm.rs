use std::collections::BTreeMap;

use bigdecimal::ToPrimitive;
use ethabi::{Token, ParamType};
use ethers::{
  types::{Address, TransactionRequest, TransactionReceipt},
  providers::Middleware,
  signers::{LocalWallet, Signer},
};

use crate::{
  typing::{Typing, ExprCode, Id, Type, Info},
  abi::Func,
  ast::{NumberSuffix, StringPrefix},
};

// pub struct Error {

// }
// pub type Result<T, E=Error> = std::result::Result<T, E>;
pub use anyhow::Result;

#[derive(Clone, PartialEq)]
pub enum ValueKind {
  Bool(bool),
  Number(bigdecimal::BigDecimal, NumberSuffix),
  Address(Address, Option<String>),
  Wallet(LocalWallet), // Custom(key)
  String(String), // String
  Bytes(Vec<u8>), // Custom(hex)
  Bytecode(Vec<u8>), // Custom(contract)
  FixedArray(Vec<ValueKind>, Type, usize),
  Array(Vec<ValueKind>, Type),
  Tuple(Vec<ValueKind>),
}

impl std::fmt::Debug for ValueKind {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Bool(arg0) => f.debug_tuple("Bool").field(arg0).finish(),
      Self::Number(arg0, arg1) => f.debug_tuple("Number").field(arg0).field(arg1).finish(),
      Self::Address(arg0, arg1) => f.debug_tuple("Address").field(arg0).field(arg1).finish(),
      Self::Wallet(arg0) => f.debug_tuple("Wallet").field(arg0).finish(),
      Self::String(arg0) => f.debug_tuple("String").field(arg0).finish(),
      Self::Bytes(arg0) => f.debug_tuple("Bytes").field(arg0).finish(),
      Self::Bytecode(arg0) => {
        // TODO: show
        f.debug_tuple("Bytecode").field(&[arg0.len()]).finish()
      }
      Self::FixedArray(arg0, arg1, arg2) => f.debug_tuple("FixedArray").field(arg0).field(arg1).field(arg2).finish(),
      Self::Array(arg0, arg1) => f.debug_tuple("Array").field(arg0).field(arg1).finish(),
      Self::Tuple(arg0) => f.debug_tuple("Tuple").field(arg0).finish(),
    }
  }
}

impl ValueKind {
  pub fn show(&self) -> String {
    const MAX_LEN: usize = 64;
    let s = format!("{:?}", self);
    if s.len() > MAX_LEN {
      format!("{}...: {}", &s[..MAX_LEN/2], self.ty())
    } else {
      s
    }
  }
  pub fn ty(&self) -> Type {
    match self {
      ValueKind::Bool(_) => Type::Bool,
      ValueKind::Number(_, suffix) => Type::Number(*suffix),
      ValueKind::Address(_, _) => Type::String(StringPrefix::Address),
      ValueKind::Wallet(_) => Type::String(StringPrefix::Key),
      ValueKind::String(_) => Type::String(StringPrefix::None),
      ValueKind::Bytes(_) => Type::String(StringPrefix::Byte),
      ValueKind::Bytecode(_) => todo!(),
      ValueKind::FixedArray(_, sub_ty, n) => Type::FixedArray(Box::new(sub_ty.clone()), *n),
      ValueKind::Array(_, _) => todo!(),
      ValueKind::Tuple(_) => todo!(),
    }
  }
}

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;

#[derive(Debug, Default)]
pub struct BuiltIn {
  pub wallet: Option<LocalWallet>,
  pub confirm_interval: Option<f64>,
}
pub struct VM {
  pub generation: BTreeMap<Id, Id>,
  pub values: BTreeMap<Id, ValueKind>,
  pub builtin: BTreeMap<String, Id>,
  pub state: BuiltIn,
  pub provider: Provider,
}

impl VM {
  pub fn new() -> Self {
    Self {
      generation: Default::default(),
      values: Default::default(),
      builtin: Default::default(),
      state: Default::default(),
      provider: Provider::try_from("http://localhost:8545").unwrap(),
    }
  }
  pub fn set_builtin(&mut self, name: &str, id: Id, value: &ValueKind) {
    match name {
      "$endpoint" => match &value {
        ValueKind::String(s) => {
          *self.provider.url_mut() = url::Url::parse(s).unwrap();
        }
        _ => unreachable!()
      }
      "$account" => match &value {
        ValueKind::Wallet(wallet) => {
          self.state.wallet = Some(wallet.clone());
        }
        _ => unreachable!()
      }
      "$confirm_interval" => match &value {
        ValueKind::Number(number, _) => {
          self.state.confirm_interval = Some(number.to_f64().unwrap());
        }
        _ => unreachable!()
      }
      _ => warn!("unknown builtin name {}", name)
    };
    self.builtin.insert(name.to_string(), id);
  }
  pub fn get_value(&self, id: Id) -> Option<&ValueKind> {
    if let Some(id) = self.generation.get(&id) {
      self.values.get(id)
    } else {
      self.values.get(&id)
    }
  }
  pub fn set_value(&mut self, id: Id, info: &Info, value: ValueKind) -> Result<()> {
    trace!("set_value: {} = {}", id, value.show());
    // let value = try_convert(info.ty(), value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    if info.display.starts_with("$") && !info.display.starts_with("$$") {
      self.set_builtin(&info.display, id, &value);
    }
    let latest = self.generation.entry(Id(id.0, 0)).or_insert(id);
    let id = Id(id.0, latest.1+1);
    self.generation.insert(Id(id.0, 0), id);
    self.values.insert(id, value);
    Ok(())
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
      let id_0 = c.get(1).unwrap().as_str().parse::<u64>().unwrap();
      let id_1_str = c.get(3).map(|i| i.as_str()).unwrap_or("0");
      let id_1 = id_1_str.parse::<u64>().unwrap();
      let id = Id(id_0, id_1);
      match vm.values.get(&id) {
        Some(a) => a.show(),
        None => format!("~{}~", id),
      }
    };
    let re = regex::Regex::new(r"\$\$(\d+)(\[(\d+)\])?").unwrap();
    let code_str = self.to_string();
    let code_str = re.replace_all(&code_str, expand);
    if code_str.len() > MAX_LEN {
      code_str[..MAX_LEN].to_string() + "..."
    } else {
      code_str.to_string()
    }
  }
}

pub fn execute(vm: &mut VM, typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    debug!("code: {} <- {}", id, info.expr.code.show_var(vm));
    match &info.expr.code {
      ExprCode::None => {
        warn!("expr is none: {:?}", id)
      }
      _ => {},
    }
    let value = execute_impl(vm, typing, &info.expr.code, Some(&info.ty()))?;
    vm.set_value(*id, info, value)?;
  }
  Ok(())
}

fn execute_impl(vm: &mut VM, typing: &Typing, code: &ExprCode, ty: Option<&Type>) -> Result<ValueKind> {
  match &code {
    ExprCode::None => {
      todo!()
    }
    ExprCode::Expr(i) => {
      let value = if let Some(value) = vm.get_value(*i) {
        value.clone()
      } else {
        anyhow::bail!("vm: copy value from {:?} failed", i);
      };
      return Ok(value)
    }
    ExprCode::Func { func, this, args, send } => {
      let args = args.iter().map(|i| vm.get_value(*i)).collect::<Option<Vec<_>>>().ok_or_else(|| anyhow::format_err!("vm: args no present"))?;
      if func.name == "constructor" && *send {
        let this = this.unwrap();
        trace!("contract name {}", &func.ns);
        let bytecode = match vm.get_value(this) {
          Some(ValueKind::Bytecode(bytes)) => bytes,
          _ => anyhow::bail!("vm: contract bytecode not present"),
        };
        let result = deploy_contract(vm, func.clone(), bytecode, &args)?;
        return Ok(result.unwrap().into());
      } else if !func.ns.starts_with("@/") {
        let result = call_global(vm, func.clone(), &args)?;
        return Ok(result);
      } else if let Some(this) = this {
        let this_addr = match vm.get_value(*this) {
          Some(ValueKind::Address(address, _)) => *address,
          _ => anyhow::bail!("vm: this not address")
        };
        trace!("this_addr: {:?} {:?}", this, this_addr);
        let result = if *send {
          send_tx(vm, this_addr, func.clone(), &args)?;
          ValueKind::Bytes(Vec::new())
        } else {
          call_tx(vm, this_addr, func.clone(), &args, ty)?
        };
        return Ok(result)
      } else {
        unreachable!()
      }
    }
    ExprCode::Number(number) => {
      let value = ValueKind::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?;
      return Ok(value)
    }
    ExprCode::String(string) => {
      let value = ValueKind::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?;
      return Ok(value)
    }
    ExprCode::List(list) => {
      let mut values = Vec::new();
      let mut sub_ty = None;
      for i in list {
        let value = execute_impl(vm, typing, i, sub_ty.as_ref())?;
        if let Some(sub_ty) = &sub_ty {
          if &value.ty() != sub_ty {
            error!("execute array sub_ty: {} != {}", sub_ty, value.ty());
          }
        } else {
          sub_ty = Some(value.ty())
        }
        values.push(value)
      }
      Ok(ValueKind::FixedArray(values, sub_ty.unwrap_or_default(), list.len()))
    },
    // _ => {
    //   warn!("skip {:?} => {:?}", id, info.expr.returns)
    // }
  }
}

fn call_global(_vm: &VM, func: Func, args: &[&ValueKind]) -> Result<ValueKind> {
  let out = match (func.ns.as_str(), func.name.as_str()) {
    ("@assert", "eq") => {
      if args[0] != args[1] {
        anyhow::bail!("vm: assert_eq failed: {:?} != {:?}", args[0], args[1])
      }
      ValueKind::Bool(true)
    }
    _ => unreachable!()
  };
  Ok(out)
}

#[tokio::main]
async fn do_send_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<Option<TransactionReceipt>> {
  if let Some(wallet) = &vm.state.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  let pending = vm.provider.send_transaction(tx, None).await?;
  trace!("pending: {:?}", pending);
  let pending = if let Some(i) = vm.state.confirm_interval {
    pending.interval(std::time::Duration::from_secs_f64(i))
  } else {
    pending
  };
  Ok(pending.await?)
}

#[tokio::main]
async fn do_call_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<ethabi::Bytes> {
  if let Some(wallet) = &vm.state.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  Ok(vm.provider.call(&tx.into(), None).await?.to_vec())
}

fn convert_to_token(input_types: &[ParamType], args: &[&ValueKind]) -> Result<Vec<Token>> {
  let result = args.iter().zip(input_types).map(|(i, abi)| i.clone().into_token(abi)).collect::<Result<_, _>>()?;
  Ok(result)
}
fn convert_from_token(ty: Option<&Type>, mut args: Vec<Token>) -> Result<ValueKind> {
  let arg = if args.len() == 1 {
    args.remove(0)
  } else {
    Token::Tuple(args)
  };
  Ok(ValueKind::from_token_ty(arg, ty)?)
}

fn send_tx(vm: &VM, this_addr: Address, func: Func, args: &[&ValueKind]) -> Result<()> {
  let tokens = convert_to_token(&func.input_types, args)?;
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  do_send_tx_sync(vm, tx)?;
  Ok(())
}

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&ValueKind], ty: Option<&Type>) -> Result<ValueKind> {
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

fn deploy_contract(vm: &VM, func: Func, bytecode: &[u8], args: &[&ValueKind]) -> Result<Option<Address>> {
  let tokens = convert_to_token(&func.input_types, args)?;
  info!("deploy_contract: {} {} to {}", func.ns, bytecode.len(), vm.provider.url());
  let mut input_data = Vec::new();
  input_data.extend_from_slice(bytecode);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  let tx = TransactionRequest::new().data(input_data);//.from(vm.builtin.account);
  let receipt = do_send_tx_sync(vm, tx)?;
  let address = receipt.and_then(|i| i.contract_address);
  Ok(address)
}
