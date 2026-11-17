// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Swap {
    struct ExactInputSingleParams {
        address tokenIn;
        address tokenOut;
        uint24 fee;
        address recipient;
        uint256 deadline;
        uint256 amountIn;
        uint256 amountOutMinimum;
        uint160 sqrtPriceLimitX96;
    }

    uint160 public lastLimit;

    function exactInputSingle(ExactInputSingleParams calldata params) external payable returns (uint256) {
        require(block.timestamp <= params.deadline, "late");
        lastLimit = params.sqrtPriceLimitX96;
        return params.amountIn;
    }
}
