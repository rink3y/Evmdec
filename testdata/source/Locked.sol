// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Locked {
    address public owner = msg.sender;
    uint256 private entered = 1;
    uint256 public open;
    mapping(address => uint256) public balances;

    function setOpen(uint256 value) external {
        require(msg.sender == owner, "owner");
        open = value;
    }

    function deposit() external payable {
        require(open != 0, "closed");
        balances[msg.sender] += msg.value;
    }

    function withdraw() external {
        require(entered == 1, "entered");
        entered = 2;
        uint256 amount = balances[msg.sender];
        balances[msg.sender] = 0;
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
        entered = 1;
    }
}
