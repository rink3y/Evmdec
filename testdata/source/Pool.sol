// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IHeld {
    function balanceOf(address who) external view returns (uint256);
}

contract Pool {
    IHeld public coin;
    uint256 public reserve;

    function sync() external {
        reserve = coin.balanceOf(address(this));
    }
}
