// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Tithe {
    mapping(address => uint256) public balanceOf;
    address public pool;
    uint256 public totalSupply;
    uint256 public last;

    function transfer(address to, uint256 amount) external returns (bool) {
        require(amount != 0, "nothing to send");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        return true;
    }

    function poke() external {
        require(block.timestamp >= last + 1 days, "not yet");
        last = block.timestamp;
        uint256 cut = balanceOf[pool] / 100;
        balanceOf[pool] -= cut;
        totalSupply -= cut;
    }
}
