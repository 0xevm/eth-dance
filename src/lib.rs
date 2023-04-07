#[macro_use]
extern crate pest_derive;

pub mod ast;

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
    println!("result: {:?}", result);
    assert!(result.is_ok());
  }
}
