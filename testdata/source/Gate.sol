// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Gate {
    address public owner;
    uint256 public testing;
    mapping(address => uint256) public drawn;

    constructor() {
        owner = msg.sender;
    }

    function tune(uint256 value) external {
        require(msg.sender == owner, "not owner");
        require(testing != 0, "not testing");
        testing = value;
    }

    function draw(uint256 ticket) external {
        require(testing == 0, "testing");
        require(uint256(keccak256(abi.encode(ticket))) < 5, "no luck");
        drawn[msg.sender] += 1;
    }
}
