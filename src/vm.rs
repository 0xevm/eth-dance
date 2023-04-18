use std::collections::BTreeMap;

use ethabi::{Token, ParamType};
use ethers::{
  types::{U256, Address, TransactionRequest, TransactionReceipt},
  providers::Middleware,
  signers::{LocalWallet, Signer},
};

use crate::{
  typing::{Typing, ExprCode, Id, Type, Info},
  abi::Func,
  convert::try_convert,
};

// pub struct Error {

// }
// pub type Result<T, E=Error> = std::result::Result<T, E>;
pub use anyhow::Result;

#[derive(Clone)]
pub struct EvmValue {
  pub token: Token,
  pub abi: ParamType,
  pub ty: Option<Type>,
}

impl std::fmt::Debug for EvmValue {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    const MAX_LEN: usize = 64;
    let s = self.token.to_string();
    let s = if s.len() > MAX_LEN {
      format!("[{}]{}...", s.len(), s[..MAX_LEN].to_string())
    } else { s };
    f.debug_struct("Value").field("token", &s).field("abi", &self.abi).field("ty", &self.ty).finish()
  }
}

impl EvmValue {
  pub fn show(&self) -> String {
    const MAX_LEN: usize = 64;
    let s = self.token.to_string();
    if s.len() > MAX_LEN {
      match &self.ty {
        Some(ty) => format!("{}...: {}", &s[..MAX_LEN/2], ty),
        None => format!("{}...", &s[..MAX_LEN]),
      }
    } else {
      s
    }
  }
}

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;
pub struct VM {
  pub values: BTreeMap<Id, EvmValue>,
  pub builtin: BTreeMap<String, EvmValue>,
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
  pub fn set_builtin(&mut self, name: &str, value: &EvmValue) {
    match name {
      "$endpoint" => match &value.token {
        Token::String(s) => {
          *self.provider.url_mut() = url::Url::parse(s).unwrap();
        }
        _ => unreachable!()
      }
      "$account" => match &value.token {
        Token::Bytes(bytes) => {
          self.wallet = Some(LocalWallet::from_bytes(bytes).unwrap());
        }
        _ => unreachable!()
      }
      "$confirm_interval" => self.confirm_interval = Some(value.try_into().unwrap()),
      _ => warn!("unknown builtin name {}", name)
    };
    self.builtin.insert(name.to_string(), value.clone());
  }
  pub fn set_value(&mut self, id: Id, info: &Info, value: EvmValue) -> Result<()> {
    trace!("set_value: {} = {}", id, value.show());
    let value = try_convert(info.ty(), value).map_err(|e| anyhow::format_err!("TryConvert: {}", e))?;
    if info.display.starts_with("$") && !info.display.starts_with("$$") {
      self.set_builtin(&info.display, &value);
    }
    self.values.insert(id, value);
    Ok(())
  }
  pub fn get_address(&self, id: Id) -> Option<Address> {
    match self.values.get(&id)?.token {
      Token::Address(addr) => Some(addr),
      _ => None,
    }
  }
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

fn execute_impl(vm: &mut VM, typing: &Typing, code: &ExprCode) -> Result<EvmValue> {
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
          Some(EvmValue { token: Token::Bytes(bytes), ..}) => bytes,
          _ => anyhow::bail!("vm: contract bytecode not present"),
        };
        let result = deploy_contract(vm, &func.ns, bytecode, &args)?;
        return Ok(result.unwrap().into());
      } else if !func.ns.starts_with("@/") {
        let result = call_global(vm, func.clone(), &args)?;
        return Ok(result);
      } else if let Some(this) = this {
        trace!("this_addr: {:?} {:?}", this, vm.get_address(*this));
        let this_addr = vm.get_address(*this).ok_or_else(|| anyhow::format_err!("vm: this not address"))?;
        let result = if *send {
          send_tx(vm, this_addr, func.clone(), &args)?
        } else {
          call_tx(vm, this_addr, func.clone(), &args)?
        };
        return Ok(result)
      } else {
        unreachable!()
      }
    }
    ExprCode::Number(number) => {
      let value = EvmValue::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?;
      return Ok(value)
    }
    ExprCode::String(string) => {
      let value = EvmValue::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?;
      return Ok(value)
    }
    ExprCode::List(list) => {
      let mut values = Vec::new();
      let mut abi = None;
      for i in list {
        let value = execute_impl(vm, typing, i)?;
        if let Some(abi) = &abi {
          if abi != &value.abi {
            error!("execute array: {} != {}", abi, value.abi);
          }
        } else {
          abi = Some(value.abi);
        }
        values.push(value.token)
      }
      Ok(EvmValue {
        abi: ParamType::FixedArray(Box::new(abi.unwrap_or(ParamType::FixedBytes(0))), values.len()),
        token: Token::FixedArray(values),
        ty: None,
      })
    },
    // _ => {
    //   warn!("skip {:?} => {:?}", id, info.expr.returns)
    // }
  }
}

fn call_global(_vm: &VM, func: Func, args: &[&EvmValue]) -> Result<EvmValue> {
  let out = match (func.ns.as_str(), func.name.as_str()) {
    ("@assert", "eq") => {
      if args[0].token != args[1].token {
        anyhow::bail!("vm: assert_eq failed: {} != {}", args[0].token, args[1].token)
      }
      vec![]
    }
    _ => unreachable!()
  };
  Ok(func.to_output(out))
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

fn send_tx(vm: &VM, this_addr: Address, func: Func, args: &[&EvmValue]) -> Result<EvmValue> {
  let tokens = args.iter().map(|i| i.token.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  do_send_tx_sync(vm, tx)?;
  Ok(EvmValue {
    token: Token::Uint(U256::zero()),
    abi: ParamType::Uint(256),
    ty: None,
  })
}

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&EvmValue]) -> Result<EvmValue> {
  let tokens = args.iter().map(|i| i.token.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("call_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let bytes = do_call_tx_sync(vm, tx)?;
  let out = ethabi::decode(&func.output_types, &bytes)?;
  let result = func.to_output(out);
  // vm.provider.
  Ok(result)
}

fn deploy_contract(vm: &VM, contract_name: &str, bytecode: &[u8], args: &[&EvmValue]) -> Result<Option<Address>> {
  let tokens = args.iter().map(|i| i.token.clone()).collect::<Vec<_>>();
  info!("deploy_contract: {} {} to {}", contract_name, bytecode.len(), vm.provider.url());
  let mut input_data = Vec::new();
  input_data.extend_from_slice(bytecode);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  let tx = TransactionRequest::new().data(input_data);//.from(vm.builtin.account);
  let receipt = do_send_tx_sync(vm, tx)?;
  let address = receipt.and_then(|i| i.contract_address);
  Ok(address)
}
