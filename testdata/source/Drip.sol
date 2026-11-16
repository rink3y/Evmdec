// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IGauge {
    function level() external view returns (uint256);
}

contract Drip {
    IGauge public gauge;

    constructor(IGauge g) payable {
        gauge = g;
    }

    function claim() external {
        uint256 level = gauge.level();
        require(level > 1000, "low");
        payable(msg.sender).transfer(level - 1000);
    }
}
