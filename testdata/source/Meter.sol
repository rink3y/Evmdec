// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface IPaid {
    function transfer(address to, uint256 amount) external returns (bool);
}

interface ICounted {
    function reserve() external view returns (uint256);
}

contract Meter {
    IPaid public coin;
    ICounted public pool;
    mapping(address => uint256) public since;

    function join() external {
        since[msg.sender] = block.timestamp;
    }

    function claim() external {
        uint256 from = since[msg.sender];
        since[msg.sender] = block.timestamp;
        coin.transfer(msg.sender, ((block.timestamp - from) << 100) / pool.reserve());
    }
}
