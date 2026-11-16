// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Treasury {
    address public owner = msg.sender;

    constructor() payable {}

    function ownerWithdraw(uint256 amount) external {
        require(msg.sender == owner, "owner");
        (bool ok, ) = owner.call{value: amount}("");
        require(ok, "send failed");
    }

    function emergency(address payable to) external {
        (bool ok, ) = to.call{value: address(this).balance}("");
        require(ok, "send failed");
    }
}
