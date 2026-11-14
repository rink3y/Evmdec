# Development incidents

Runtime bytecode to develop rules on. `flawed/` holds one contract for each of 231 public
incidents and `sound/` holds 55 contracts in steady use for over three years with no known
flaw. `manifest.json` gives the address, chain and year of each, and for a flawed contract
the classes of its flaw.

This set is the second third of the same incident index the held-out set in
`testdata/heldout` is taken from, collected the same way by `corpus/heldout_collect.py` with
`--set incidents` and `--offset 1`. No contract and no incident is in both sets.

The two sets have opposite uses. Here every report may be read, every miss may be studied,
and a rule may be shaped until it finds what it should on these contracts. The held-out set
is only scored. A rule built here is worth what it then does there.

Score this set with `python3 corpus/heldout_bench.py --set incidents`. The name of each
flawed contract is the page name at <https://crypto.training/hacks/>, where the incident is
described.
