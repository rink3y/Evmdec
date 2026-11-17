// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Calls {
    struct Proposal {
        address proposer;
        string[] signatures;
    }

    mapping(uint256 => Proposal) proposals;

    function add(uint256 id, string calldata signature) external {
        proposals[id].proposer = msg.sender;
        proposals[id].signatures.push(signature);
    }

    function signatureLength(uint256 id, uint256 i) external view returns (uint256) {
        return bytes(proposals[id].signatures[i]).length;
    }
}
