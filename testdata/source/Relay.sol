// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Relay {
    address public owner = msg.sender;

    function withdraw(uint256 amount) external {
        require(msg.sender == owner);
        payable(msg.sender).transfer(amount);
    }

    function claim(uint256 amount, bytes calldata order) external {
        uint256 deadline = abi.decode(order, (uint256));
        require(deadline >= block.timestamp);
        payable(msg.sender).transfer(amount);
    }
}
