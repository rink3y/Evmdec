// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

contract Ballot {
    struct Receipt {
        bool hasVoted;
        uint8 support;
        uint96 votes;
    }

    struct Proposal {
        uint256 forVotes;
        uint256 againstVotes;
        mapping(address => Receipt) receipts;
    }

    mapping(uint256 => Proposal) proposals;

    function vote(uint256 id, uint8 support, uint96 votes) external {
        Receipt storage r = proposals[id].receipts[msg.sender];
        require(!r.hasVoted, "voted");
        r.hasVoted = true;
        r.support = support;
        r.votes = votes;
        if (support == 1) {
            proposals[id].forVotes += votes;
        } else {
            proposals[id].againstVotes += votes;
        }
    }

    function receipt(uint256 id, address who) external view returns (bool, uint8, uint96) {
        Receipt storage r = proposals[id].receipts[who];
        return (r.hasVoted, r.support, r.votes);
    }
}
