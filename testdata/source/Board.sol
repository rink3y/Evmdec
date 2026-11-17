// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Board {
    address public owner = msg.sender;

    struct Cell {
        uint256 x;
        uint256 y;
        uint256 pay;
    }

    function withdraw(uint256 amount) external {
        require(msg.sender == owner);
        payable(msg.sender).transfer(amount);
    }

    function write(Cell[] calldata cells) external {
        for (uint256 i = 0; i < cells.length; i++) {
            require(cells[i].x < 100 && cells[i].y < 100);
            payable(msg.sender).transfer(cells[i].pay);
        }
    }
}
