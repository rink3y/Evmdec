// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Bank {
    mapping(address => uint256) public balances;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function withdraw() external {
        uint256 amount = balances[msg.sender];
        require(amount > 0, "nothing");
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
        unchecked {
            balances[msg.sender] = 0;
        }
    }
}
