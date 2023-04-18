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
  ast::NumberSuffix,
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
      Self::Bytecode(_arg0) => {
        // TODO: show
        f.debug_tuple("Bytecode").finish()
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
      match &self.ty() {
        Some(ty) => format!("{}...: {}", &s[..MAX_LEN/2], ty),
        None => format!("{}...", &s[..MAX_LEN]),
      }
    } else {
      s
    }
  }
  pub fn ty(&self) -> Option<Type> {
    None
  }
}

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;
pub struct VM {
  pub values: BTreeMap<Id, ValueKind>,
  pub builtin: BTreeMap<String, ValueKind>,
  pub wallet: Option<LocalWallet>,
  pub confirm_interval: Option<f64>,
  pub provider: Provider,
}

impl VM {
  pub fn new() -> Self {
    Self {
      values: Default::default(),
      builtin: Default::default(),
      wallet: None,
      confirm_interval: None,
      provider: Provider::try_from("http://localhost:8545").unwrap(),
    }
  }
  pub fn set_builtin(&mut self, name: &str, value: &ValueKind) {
    match name {
      "$endpoint" => match &value {
        ValueKind::String(s) => {
          *self.provider.url_mut() = url::Url::parse(s).unwrap();
        }
        _ => unreachable!()
      }
      "$account" => match &value {
        ValueKind::Wallet(wallet) => {
          self.wallet = Some(wallet.clone());
        }
        _ => unreachable!()
      }
      "$confirm_interval" => match &value {
        ValueKind::Number(number, _) => {
          self.confirm_interval = Some(number.to_f64().unwrap());
        }
        _ => unreachable!()
      }
      _ => warn!("unknown builtin name {}", name)
    };
    self.builtin.insert(name.to_string(), value.clone());
  }
  pub fn set_value(&mut self, id: Id, info: &Info, value: ValueKind) -> Result<()> {
    trace!("set_value: {} = {}", id, value.show());
    // let value = try_convert(info.ty(), value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    if info.display.starts_with("$") && !info.display.starts_with("$$") {
      self.set_builtin(&info.display, &value);
    }
    self.values.insert(id, value);
    Ok(())
  }
  // pub fn get_address(&self, id: Id) -> Option<Address> {
  //   match self.values.get(&id)?.token {
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
      let id = Id(c.get(1).unwrap().as_str().parse::<u64>().unwrap());
      match vm.values.get(&id) {
        Some(a) => a.show(),
        None => format!("~{}~", id),
      }
    };
    let re = regex::Regex::new(r"\$\$(\d+)").unwrap();
    let code_str = self.to_string();
    let code_str = re.replace(&code_str, expand);
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
    let value = execute_impl(vm, typing, &info.expr.code)?;
    vm.set_value(*id, info, value)?;
  }
  Ok(())
}

fn execute_impl(vm: &mut VM, typing: &Typing, code: &ExprCode) -> Result<ValueKind> {
  match &code {
    ExprCode::None => {
      todo!()
    }
    ExprCode::Expr(i) => {
      let value = if let Some(value) = vm.values.get(i) {
        value.clone()
      } else {
        anyhow::bail!("vm: copy value from {:?} failed", i);
      };
      return Ok(value)
    }
    ExprCode::Func { func, this, args, send } => {
      let args = args.iter().map(|i| vm.values.get(i)).collect::<Option<Vec<_>>>().ok_or_else(|| anyhow::format_err!("vm: args no present"))?;
      if func.name == "constructor" && *send {
        let this = this.unwrap();
        trace!("contract name {}", &func.ns);
        let bytecode = match vm.values.get(&this) {
          Some(ValueKind::Bytecode(bytes)) => bytes,
          _ => anyhow::bail!("vm: contract bytecode not present"),
        };
        let result = deploy_contract(vm, func.clone(), bytecode, &args)?;
        return Ok(result.unwrap().into());
      } else if !func.ns.starts_with("@/") {
        let result = call_global(vm, func.clone(), &args)?;
        return Ok(result);
      } else if let Some(this) = this {
        let this_addr = match vm.values.get(this) {
          Some(ValueKind::Address(address, _)) => *address,
          _ => anyhow::bail!("vm: this not address")
        };
        trace!("this_addr: {:?} {:?}", this, this_addr);
        let result = if *send {
          send_tx(vm, this_addr, func.clone(), &args)?;
          ValueKind::Bytes(Vec::new())
        } else {
          call_tx(vm, this_addr, func.clone(), &args)?
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
      let mut ty = None;
      for i in list {
        let value = execute_impl(vm, typing, i)?;
        if let Some(ty) = &ty {
          // if abi != &value.abi {
          //   error!("execute array: {} != {}", abi, value.abi);
          // }
        } else {
          ty = None//Some(value.abi);
        }
        values.push(value)
      }
      Ok(ValueKind::FixedArray(values, ty.unwrap_or_default(), list.len()))
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
  if let Some(wallet) = &vm.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  let pending = vm.provider.send_transaction(tx, None).await?;
  trace!("pending: {:?}", pending);
  let pending = if let Some(i) = vm.confirm_interval {
    pending.interval(std::time::Duration::from_secs_f64(i))
  } else {
    pending
  };
  Ok(pending.await?)
}

#[tokio::main]
async fn do_call_tx_sync(vm: &VM, mut tx: TransactionRequest) -> Result<ethabi::Bytes> {
  if let Some(wallet) = &vm.wallet {
    tx = tx.from(wallet.address());
    // wallet.sign_transaction_sync(&tx)?;
  }
  Ok(vm.provider.call(&tx.into(), None).await?.to_vec())
}

fn convert_to_token(input_types: &[ParamType], args: &[&ValueKind]) -> Result<Vec<Token>> {
  let result = args.iter().zip(input_types).map(|(i, abi)| i.clone().into_token(abi)).collect::<Result<_, _>>()?;
  Ok(result)
}
fn convert_from_token(output_types: &[ParamType], args: &[Token]) -> Result<ValueKind> {
  let mut values = args.iter().zip(output_types).map(|(i, abi)| ValueKind::from_token(i, abi)).collect::<Result<Vec<_>, _>>()?;
  if values.len() == 1 {
    return Ok(values.remove(0))
  }
  Ok(ValueKind::Tuple(values))
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

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&ValueKind]) -> Result<ValueKind> {
  let tokens = convert_to_token(&func.input_types, args)?;
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("call_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let bytes = do_call_tx_sync(vm, tx)?;
  let out = ethabi::decode(&func.output_types, &bytes)?;
  let result = convert_from_token(&func.output_types, &out)?;
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
