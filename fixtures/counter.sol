pragma solidity ^0.8.19;

contract CounterFactory {
  function create(uint, uint) external returns(address) {
    return address(0);
  }
}

contract Counter {
  function set_admin(address) external {
  }
}
