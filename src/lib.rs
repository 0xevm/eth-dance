#[macro_use] extern crate log;
#[macro_use] extern crate pest_derive;

pub mod abi;
pub mod ast;
pub mod typing;
pub mod vm;

pub fn add(left: usize, right: usize) -> usize {
  left + right
}

#[cfg(test)]
mod tests {
  use std::rc::Rc;

  use super::*;

  #[test]
  fn it_works() -> anyhow::Result<()> {
    flexi_logger::Logger::try_with_env_or_str("eth_caller=debug,ethers=debug").unwrap().start().ok();
    let input = include_str!("../fixtures/test.conf");
    let result = match ast::parse(input) {
      Ok(result) => result,
      Err(e) => {
        let line_index = Rc::new(input.lines().map(|i| i.as_ptr() as usize - input.as_ptr() as usize).collect::<Vec<_>>());
        for i in e.inner_errors() {
          error!("parse error: {}\n{:?}", i.show_pos(input, line_index.clone()), i);
        }
        anyhow::bail!("parse failed")
      }
    };
    result.iter().for_each(|i| info!("{:?}", i));
    let mut state = typing::Typing::new();

    let contract1 = abi::load_abi("CounterFactory", include_str!("../out/counter.sol/CounterFactory.json"))?;
    let contract2 = abi::load_abi("Counter", include_str!("../out/counter.sol/Counter.json"))?;
    info!("{:?}", contract1);
    state.add_scope(contract1);
    state.add_scope(contract2);
    let result = typing::parse_file(&mut state, &result);
    for (id, info) in &state.infos {
      debug!("{:?}{}: [{:?}<={:?}] {}", id, info.display, info.should, info.expr.returns, info.expr.t);
    }
    match result {
      Ok(result) => result,
      Err(e) => {
        let line_index = Rc::new(input.lines().map(|i| i.as_ptr() as usize - input.as_ptr() as usize).collect::<Vec<_>>());
        for i in e.inner_errors() {
          error!("typing error: {}\n{:?}", i.show_pos(input, line_index.clone()), i);
        }
        anyhow::bail!("parse failed")
      }
    };

    let mut vm = vm::VM::new();
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
      warn!("name: {} {:?}", name, id);
      let value = vm.values.get(id).unwrap();
      info!("vm: {:?} = [{}] {}", name, value.abi, value.value);
    }
    Ok(())
  }
}
