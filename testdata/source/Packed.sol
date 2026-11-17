// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Packed {
    struct Allowance {
        uint160 amount;
        uint48 expiration;
        uint48 nonce;
    }

    mapping(address => mapping(address => Allowance)) public allowed;

    function approve(address spender, uint160 amount, uint48 expiration) external {
        Allowance storage a = allowed[msg.sender][spender];
        a.amount = amount;
        a.expiration = expiration;
    }

    function spend(address owner, uint160 amount) external {
        Allowance storage a = allowed[owner][msg.sender];
        require(block.timestamp <= a.expiration, "expired");
        require(amount <= a.amount, "short");
        a.amount -= amount;
    }

    function bump() external {
        allowed[msg.sender][msg.sender].nonce += 1;
    }
}
