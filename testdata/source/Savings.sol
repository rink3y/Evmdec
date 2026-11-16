// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Savings {
    uint256 public ratePerDay;
    mapping(address => uint256) public paidIn;
    mapping(address => uint256) public since;

    constructor(uint256 rate) payable {
        ratePerDay = rate;
    }

    function deposit() external payable {
        require(paidIn[msg.sender] == 0, "open");
        paidIn[msg.sender] = msg.value;
        since[msg.sender] = block.timestamp;
    }

    function close() external {
        uint256 amount = paidIn[msg.sender];
        require(amount != 0, "none");
        require(block.timestamp >= since[msg.sender] + 1 days, "early");
        uint256 interest = (amount * ratePerDay * (block.timestamp - since[msg.sender])) / 1 days / 10000;
        paidIn[msg.sender] = 0;
        payable(msg.sender).transfer(amount + interest);
    }
}
