// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Late {
    address public owner;
    uint256 public opened;
    uint256 public rate;

    constructor() {
        owner = msg.sender;
    }

    function tune(uint256 value) external {
        require(msg.sender == owner, "owner");
        rate = value;
    }

    function open() external {
        opened = block.timestamp;
    }

    function claim() external {
        require(opened != 0 && block.timestamp - opened >= 1 days, "early");
        owner = msg.sender;
    }
}
