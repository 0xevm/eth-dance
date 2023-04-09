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
  #[test]
  fn it_works() -> anyhow::Result<()> {
    Ok(())
  }
}
