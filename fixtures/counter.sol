pragma solidity ^0.8.19;

contract CounterFactory {
  function create(uint, uint) external {
  }
  function get_counter() external view returns(address) {
    return address(0);
  }
}

contract Counter {
  uint256 public sum = 0;
  function set_admin(address) external {
  }
  function add(uint i) external {
    sum += i;
  }
}
