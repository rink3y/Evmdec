// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface ICoin {
    function transfer(address to, uint256 amount) external returns (bool);
}

interface IPool {
    function reserve() external view returns (uint256);
}

contract Desk {
    ICoin public coin;
    IPool public pool;

    function buy() external payable {
        require(msg.value == 1 ether, "price");
        coin.transfer(msg.sender, pool.reserve() / 1000);
    }
}
