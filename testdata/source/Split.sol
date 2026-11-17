// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Split {
    address public owner = msg.sender;

    function withdraw(uint256 amount) external {
        require(msg.sender == owner);
        payable(msg.sender).transfer(amount);
    }

    function pay(bytes calldata order) external {
        (uint256 share, uint256 whole) = abi.decode(order, (uint256, uint256));
        payable(msg.sender).transfer(share);
        unchecked {
            payable(owner).transfer(whole - share);
        }
    }
}
