// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IReceiver {
    function receiveApproval(address from, uint256 value) external;
}

contract Allow {
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function deposit() external payable {
        balanceOf[msg.sender] += msg.value;
    }

    function withdraw(uint256 value) external {
        balanceOf[msg.sender] -= value;
        payable(msg.sender).transfer(value);
    }

    function approveAndCall(address spender, uint256 value) external {
        allowance[msg.sender][spender] = value;
        IReceiver(spender).receiveApproval(msg.sender, value);
    }

    function transferFrom(address from, address to, uint256 value) external {
        allowance[from][msg.sender] -= value;
        balanceOf[from] -= value;
        balanceOf[to] += value;
    }
}
