// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

interface Source {
    function one() external view returns (uint256);

    function three() external view returns (uint256, uint256, uint256);
}

contract Asker {
    Source public source;
    mapping(address => uint256) public seen;

    constructor(Source from) {
        source = from;
    }

    function ask() external {
        uint256 first = source.one();
        (uint256 a, uint256 b, uint256 c) = source.three();
        seen[msg.sender] = first + a + b + c;
    }
}
