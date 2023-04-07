#[macro_use] extern crate log;
#[macro_use] extern crate pest_derive;

pub mod ast;
pub mod global;
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
    flexi_logger::Logger::try_with_env_or_str("eth_caller=debug").unwrap().start().unwrap();
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
    state.add_scope("CounterFactory", Default::default());
    match typing::parse_file(&mut state, &result) {
      Ok(result) => result,
      Err(e) => {
        let line_index = Rc::new(input.lines().map(|i| i.as_ptr() as usize - input.as_ptr() as usize).collect::<Vec<_>>());
        for i in e.inner_errors() {
          error!("typing error: {}\n{:?}", i.show_pos(input, line_index.clone()), i);
        }
        anyhow::bail!("parse failed")
      }
    };
    Ok(())
  }
}
