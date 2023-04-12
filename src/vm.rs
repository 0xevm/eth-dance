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

#[derive(Debug, Clone)]
pub struct Value {
  pub token: Token,
  pub abi: ParamType,
  pub ty: Option<Type>,
}

pub type Provider = ethers::providers::Provider<ethers::providers::Http>;
pub struct VM {
  pub values: BTreeMap<Id, Value>,
  pub builtin: BTreeMap<String, Value>,
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
  pub fn set_builtin(&mut self, name: &str, value: &Value) {
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
  pub fn set_value(&mut self, id: Id, info: &Info, value: Value) -> Result<()> {
    trace!("set_value: {:?} = {}", id, value.token);
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

pub fn execute(vm: &mut VM, typing: &Typing) -> Result<()> {
  for (id, info) in &typing.infos {
    match &info.expr.code {
      ExprCode::None => {
        warn!("expr is none: {:?}", id)
      }
      ExprCode::Expr(i) => {
        let value = if let Some(value) = vm.values.get(i) {
          value.clone()
        } else {
          anyhow::bail!("vm: copy value from {:?} failed", i);
        };
        vm.set_value(*id, info, value)?;
      }
      ExprCode::Func { func, this, args, send } => {
        let args = args.iter().map(|i| vm.values.get(i)).collect::<Option<Vec<_>>>().ok_or_else(|| anyhow::format_err!("vm: args no present"))?;
        if func.ns == "@Global" && func.name == "deploy" && *send {
          let this = this.unwrap();
          let contract_name = match typing.get_info_view(this).ty() {
            Type::ContractType(name) => name,
            t => {
              anyhow::bail!("vm: deploy args not contract {:?}", t)
            }
          };
          trace!("contract name {}", contract_name);
          let bytecode = match vm.values.get(&this) {
            Some(Value { token: Token::Bytes(bytes), ..}) => bytes,
            _ => anyhow::bail!("vm: contract bytecode not present"),
          };
          let result = deploy_contract(vm, contract_name, bytecode, &args)?;
          vm.set_value(*id, info, result.unwrap().into())?;
        } else if !func.ns.starts_with("@/") {
          let result = call_global(vm, func.clone(), &args)?;
          vm.set_value(*id, info, result)?;

        } else if let Some(this) = this {
          trace!("this_addr: {:?} {:?} {:?}", id, this, vm.get_address(*this));
          let this_addr = vm.get_address(*this).ok_or_else(|| anyhow::format_err!("vm: this not address"))?;
          let result = if *send {
            send_tx(vm, this_addr, func.clone(), &args)?
          } else {
            call_tx(vm, this_addr, func.clone(), &args)?
          };
          vm.set_value(*id, info, result)?;
        } else {
          unreachable!()
        }
      }
      ExprCode::Number(number) => {
        let value = Value::try_from(number.clone()).map_err(|e| anyhow::format_err!("TypedNumber: {}", e))?;
        vm.set_value(*id, info, value)?;
      }
      ExprCode::String(string) => {
        let value = Value::try_from(string.clone()).map_err(|e| anyhow::format_err!("TypedString: {}", e))?;
        vm.set_value(*id, info, value)?;
      }
      // _ => {
      //   warn!("skip {:?} => {:?}", id, info.expr.returns)
      // }
    }
  }
  Ok(())
}

fn call_global(_vm: &VM, func: Func, args: &[&Value]) -> Result<Value> {
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

fn send_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value]) -> Result<Value> {
  let tokens = args.iter().map(|i| i.token.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  do_send_tx_sync(vm, tx)?;
  Ok(Value {
    token: Token::Uint(U256::zero()),
    abi: ParamType::Uint(256),
    ty: None,
  })
}

fn call_tx(vm: &VM, this_addr: Address, func: Func, args: &[&Value]) -> Result<Value> {
  let tokens = args.iter().map(|i| i.token.clone()).collect::<Vec<_>>();
  let mut input_data = Vec::new();
  input_data.extend_from_slice(&func.selector);
  input_data.extend_from_slice(&ethabi::encode(&tokens));
  debug!("send_tx: {} {}", this_addr, hex::encode(&input_data));
  let tx = TransactionRequest::new().to(this_addr).data(input_data);//.from(vm.builtin.account);
  let bytes = do_call_tx_sync(vm, tx)?;
  let out = ethabi::decode(&func.output_types, &bytes)?;
  let result = func.to_output(out);
  // vm.provider.
  Ok(result)
}

fn deploy_contract(vm: &VM, contract_name: &str, bytecode: &[u8], args: &[&Value]) -> Result<Option<Address>> {
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
