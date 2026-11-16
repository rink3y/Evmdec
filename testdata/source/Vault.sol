// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Vault {
    address public owner;
    mapping(address => uint256) public balances;

    constructor() {
        owner = msg.sender;
    }

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw(uint256 amount) external {
        require(balances[msg.sender] >= amount, "too much");
        balances[msg.sender] -= amount;
        payable(msg.sender).transfer(amount);
    }

    function setOwner(address next) external {
        owner = next;
    }

    function sweep(address payable to) external {
        to.transfer(address(this).balance);
    }

    function rescue(address payable to) external {
        require(msg.sender == owner, "not owner");
        to.transfer(address(this).balance);
    }
}
