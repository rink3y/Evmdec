// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Vest {
    mapping(address => uint256) public since;
    mapping(address => uint256) public bal;

    function put() external payable {
        bal[msg.sender] += msg.value;
        since[msg.sender] = block.timestamp;
    }

    function take() external {
        require(block.timestamp - since[msg.sender] >= 7 days, "early");
        pay();
    }

    function takeByDays() external {
        require((block.timestamp - since[msg.sender]) / 1 days > 30, "early");
        pay();
    }

    function pay() private {
        uint256 b = bal[msg.sender];
        require(b != 0, "none");
        bal[msg.sender] = 0;
        payable(msg.sender).transfer(b);
    }
}
