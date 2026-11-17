// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Gauge {
    uint256 public level;

    function raise(uint256 by) external {
        level += by;
    }
}
