#[macro_use] extern crate log;

use std::{rc::Rc, path::Path};

use anyhow::Result;
use clap::Parser;
use eth_dance::{
  abi::load_abi,
  ast,
  typing::{self, Typing},
  vm::{self, VM}
};

#[derive(clap::Parser)]
struct Opts {
  #[arg(short, long, action = clap::ArgAction::Count)]
  verbose: u8,
  path: String,
}

fn run<P: AsRef<Path>>(path: P) -> Result<()> {
  let input = std::fs::read_to_string(path.as_ref())?;
  let result = match ast::parse(&input) {
    Ok(result) => result,
    Err(e) => {
      let line_index = Rc::new(input.lines().map(|i| i.as_ptr() as usize - input.as_ptr() as usize).collect::<Vec<_>>());
      for i in e.inner_errors() {
        error!("parse error: {}\n{:?}", i.show_pos(&input, line_index.clone()), i);
      }
      anyhow::bail!("parse failed")
    }
  };
  result.iter().for_each(|i| info!("{:?}", i));
  let mut state = Typing::new();

  let contract1 = load_abi("CounterFactory", include_str!("../out/counter.sol/CounterFactory.json"))?;
  let contract2 = load_abi("Counter", include_str!("../out/counter.sol/Counter.json"))?;
  info!("{:?}", contract1);
  state.add_scope(contract1);
  state.add_scope(contract2);
  let result = typing::parse_file(&mut state, &result);
  for (id, info) in &state.infos {
    debug!("{:?}{}: [{:?}<={:?}] {}", id, info.display, info.should, info.expr.returns, info.expr.code);
  }
  match result {
    Ok(result) => result,
    Err(e) => {
      let line_index = Rc::new(input.lines().map(|i| i.as_ptr() as usize - input.as_ptr() as usize).collect::<Vec<_>>());
      for i in e.inner_errors() {
        error!("typing error: {}\n{:?}", i.show_pos(&input, line_index.clone()), i);
      }
      anyhow::bail!("parse failed")
    }
  };

  let mut vm = VM::new();
  let result = vm::execute(&mut vm, &state);
  for (id, value) in &vm.builtin {
    debug!("vm: {:?} = {:?}", id, value);
  }
  for (id, value) in &vm.values {
    debug!("vm: {:?} = {:?}", id, value);
  }
  debug!("last_id: {:?}", state.last_id);
  result?;
  for (name, id) in &state.found {
    // warn!("name: {} {:?}", name, id);
    let value = vm.values.get(id).unwrap();
    info!("vm: {:?} = [{}] {}", name, value.abi, value.token);
  }
  Ok(())
}

fn main() -> Result<()> {
  let opts = Opts::parse();
  let verbose_str = match opts.verbose {
    0 => "info",
    1 => "debug",
    _ => "trace",
  };
  flexi_logger::Logger::try_with_env_or_str(format!("cli={v},eth_dance={v},ethers=debug", v=verbose_str)).unwrap().start().ok();

  run(&opts.path)?;
  Ok(())
}
