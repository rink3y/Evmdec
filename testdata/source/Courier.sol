// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Courier {
    address public owner = msg.sender;

    function withdraw(uint256 amount) external {
        require(msg.sender == owner);
        payable(msg.sender).transfer(amount);
    }

    function deliver(bytes calldata order) external {
        (address to, uint256 amount, uint256 deadline) = abi.decode(order, (address, uint256, uint256));
        require(deadline >= block.timestamp);
        payable(to).transfer(amount);
    }

    function relay(address target, bytes calldata data) external {
        (bool ok, ) = target.call(data);
        ok;
    }
}
