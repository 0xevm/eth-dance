#[macro_use] extern crate log;

use std::{rc::Rc, path::Path};

use anyhow::Result;
use clap::Parser;
use eth_dance::{
  ast,
  typing::{self, Typing, Type},
  vm::{self, VM}, out
};

#[derive(clap::Parser)]
struct Opts {
  #[arg(short, long, action = clap::ArgAction::Count)]
  verbose: u8,
  #[arg(short, long)]
  workdir: Option<String>,
  #[arg(short, long, default_value = "out")]
  out: String,
  filename: String,
}

fn run<P: AsRef<Path>>(workdir: P, opts: &Opts) -> Result<()> {
  let input = std::fs::read_to_string(&opts.filename)?;
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
  result.iter().for_each(|i| trace!("{:?}", i));
  let mut state = Typing::new(Path::new(&opts.filename).to_path_buf(), workdir.as_ref().to_path_buf());

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
      anyhow::bail!("typing failed")
    }
  };
  let ir = out::ir::to_ir(&state);
  std::fs::create_dir_all(&opts.out)?;
  std::fs::write(format!("{}/ir.txt", opts.out), ir.join("\n\n"))?;

  let mut vm = VM::new();
  let result = vm::execute(&mut vm, &state);
  for (id, value) in &vm.builtin {
    debug!("vm: {:?} = {:?}", id, value);
  }
  for (id, value) in &vm.values {
    trace!("vm: {:?} = {:?}", id, value);
  }
  debug!("last_id: {:?}", state.last_id);
  result?;
  for (name, id) in &state.found {
    // warn!("name: {} {:?}", name, id);
    let value = vm.values.get(id).unwrap();
    match value.ty {
      Some(Type::ContractType(_)) => {
        if let ethabi::Token::Bytes(i) = &value.token {
          info!("vm: {:?} = [{}] hash={} len={}", name, value.abi, ethabi::Token::FixedBytes(ethers::utils::keccak256(i).to_vec()), i.len());
          continue;
        }
      }
      _ => {},
    }
    info!("vm: {:?} = [{}] {}", name, value.abi, value.token);
  }
  let cache = out::cache::from_vm(&vm, &state);
  std::fs::write(format!("{}/cache.toml", opts.out), toml::to_string_pretty(&cache)?)?;

  let cache: out::cache::Output = toml::from_str(&std::fs::read_to_string(format!("{}/cache.toml", opts.out))?)?;
  let contracts = out::contract::gen(&cache.vars);
  std::fs::write(format!("{}/contracts.json", opts.out), serde_json::to_string_pretty(&contracts)?)?;
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
  let workdir = match &opts.workdir {
    Some(dir) => Path::new(dir).to_path_buf(),
    None => {
      let mut current_dir = std::env::current_dir()?;
      while !current_dir.join("foundry.toml").exists() {
        if let Some(parent) = current_dir.parent() {
          current_dir = parent.to_path_buf();
        } else {
          current_dir = std::env::current_dir()?;
          warn!("cannot found foundry, use {}", current_dir.to_string_lossy());
          break
        }
      }
      debug!("found foundry, use {}", current_dir.to_string_lossy());
      current_dir.to_path_buf()
    }
  };
  run(workdir, &opts).unwrap();
  Ok(())
}
