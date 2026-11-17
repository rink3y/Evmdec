// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Cached {
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;

    constructor() {
        totalSupply = 1_000_000 ether;
        balanceOf[msg.sender] = totalSupply;
    }

    function transfer(address to, uint256 amount) external returns (bool) {
        uint256 senderBefore = balanceOf[msg.sender];
        uint256 receiverBefore = balanceOf[to];
        require(senderBefore >= amount, "balance");
        balanceOf[msg.sender] = senderBefore - amount;
        balanceOf[to] = receiverBefore + amount;
        return true;
    }
}
