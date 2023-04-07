use std::collections::{BTreeSet, BTreeMap};

#[macro_use]
extern crate pest_derive;

pub mod ast;
pub mod global;
pub mod typing;
pub mod vm;

pub fn add(left: usize, right: usize) -> usize {
  left + right
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    let input = include_str!("../fixtures/test.conf");
    let result = ast::parse(input);
    match &result {
      Ok(v) => v.iter().for_each(|i| println!("{:?}", i)),
      Err(e) => println!("{:?}", e),
    }
    assert!(result.is_ok());
  }
}
