# Held-out set

Runtime bytecode the analyzer was not built on. It exists to answer one question honestly:
how well does the analyzer do on contracts it has never seen?

## Rule of use

Nothing is tuned against this set. Rules are developed on `testdata/vuln`, `testdata/mainnet`
and the labelled fixtures in `testdata/rules`. This set is only scored, with
`python3 corpus/heldout_bench.py`.

A miss here says which kind of flaw the analyzer does not reach. The fix is a general rule,
shown on a synthetic fixture or on the development corpus, and then scored here again. A
change made to turn one contract of this set from a miss into a hit makes the score
meaningless for every other contract.

The table in `corpus/heldout_bench.py` that maps a flaw class to the rule families that count
as finding it was written before any contract of the set was analysed. A new rule is added to
the family it belongs to. The table is not edited to fit a result.

## What is in it

`flawed/` holds one contract for each of 234 public incidents from 2017 to 2026 on seven
chains. `sound/` holds 101 contracts with no known flaw. `manifest.json` gives the address,
chain and year of each, and for a flawed contract the classes of its flaw.

The incidents and their classes come from the index of reproduced incidents at
<https://crypto.training/hacks/>, which builds on the DeFiHackLabs registry. The name of each
flawed contract is the page name there, so `2023-07-conic02` is described at
`https://crypto.training/hacks/2023-07-conic02/`. Only addresses and class labels are taken
from the pages.

## How it was chosen

No step looks at what the analyzer reports. `corpus/heldout_collect.py` does all of it.

Flawed contracts:

1. The dated incidents are sorted by name and every third one is taken, starting with the
   first. The other two thirds are untouched and can become a second and a third set.
2. Each page lists the flawed contract first. That address is used, unless it is a thin
   forwarder to other code, in which case the next listed address is tried.
3. An incident is dropped when its address has no code today, its chain has no public
   endpoint, the address was already used in development, the same code is listed by
   several incidents, the page gives no class, or the flaw is a leaked key or an owner's own
   action and so is not in the code.

Contracts with no known flaw:

1. Blocks from September 2022 to April 2023 and blocks from the last month are sampled on
   Ethereum and BNB Chain. A contract called in both samples has been in steady use for more
   than three and a half years.
2. The most used are taken, through an EIP-1967 proxy to the code behind it where one is in
   front. Addresses used in development or listed on any fetched incident page are left out.

## What the score can and cannot say

- A flawed contract counts as found when the report has a finding at high or above from a
  rule family that matches one of its classes. The label is the kind of flaw, not the
  function, so a finding of the right kind in the wrong function still counts. The recall
  printed is therefore an upper bound.
- The code is what the address holds today. A contract that was upgraded behind a proxy after
  its incident is fetched as the logic address the page names, not the current one.
- "No known flaw" means long use and no listed incident. It is not a proof. A finding at high
  or above on such a contract is counted as a false alarm, and a few of them may be true.
- The sound half is mostly Ethereum. The flawed half is nearly half BNB Chain.
- Several incidents need a second contract, a price moved in the same transaction, or state
  that the bytecode alone does not show. They are kept, because a real user brings exactly
  such contracts.
