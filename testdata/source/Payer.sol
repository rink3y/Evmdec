// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface IPool {
    function token() external view returns (address);
}

interface IERC20 {
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

contract Payer {
    function settle(uint256 owed, bytes calldata data) external {
        (address payer, address pool) = abi.decode(data, (address, address));
        require(msg.sender == pool);
        require(msg.sender.code.length > 0);
        address token = IPool(msg.sender).token();
        require(IERC20(token).transferFrom(payer, msg.sender, owed));
    }
}
