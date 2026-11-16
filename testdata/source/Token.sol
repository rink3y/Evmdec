// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Token {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => uint256) public locked;

    constructor() {
        totalSupply = 1_000_000 ether;
        balanceOf[msg.sender] = totalSupply;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function lock(uint256 amount) external {
        balanceOf[msg.sender] -= amount;
        locked[msg.sender] += amount;
    }

    function unlock() external {
        uint256 amount = locked[msg.sender];
        locked[msg.sender] = 0;
        balanceOf[msg.sender] += amount;
    }

    function burn(address from, uint256 amount) external {
        balanceOf[from] -= amount;
        totalSupply -= amount;
    }
}
