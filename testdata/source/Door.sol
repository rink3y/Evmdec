// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Door {
    mapping(address => uint256) public bal;

    function put() external payable {
        address who = msg.sender;
        bytes32 hash;
        assembly {
            hash := extcodehash(who)
        }
        bool plain = hash == 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        require(plain || hash == 0, "contract");
        bal[who] += msg.value;
    }
}
