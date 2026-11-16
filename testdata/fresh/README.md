# Fresh set

Runtime bytecode of 213 contracts from public incidents, taken from the third of the index at
<https://crypto.training/hacks/> that neither `testdata/heldout` nor `testdata/incidents`
uses. It was collected after the checks of the research branch were built, to see how far
they carry.

## Rule of use

The same as the held-out set. Nothing is tuned against it and no contract in it is read to
shape the analyzer. It is only scored, by reviewers who return counts.

## How it was chosen

`corpus/heldout_collect.py` did all of it, and no step looks at what the analyzer reports.

1. The dated incidents are sorted by name and every third one is taken, starting with the
   third: `pages --step 3 --offset 2`. That gives 324 pages.
2. `flawed` reads each page and fetches the code of the first listed contract that has code
   today and is not a forwarder. 240 remain. The rest list no contract, sit on a chain with
   no public endpoint, or name a contract another set already holds.
3. `assemble --only logic,access-control,defi,arithmetic,reentrancy,auth,loss-of-funds,accounting,data,economic,math`
   keeps an incident when one of its classes is in a category named there, and drops code
   that several incidents share. 213 remain.

There are no contracts without a known flaw in this set. False alarms are measured on the
sound contracts of the other two sets.

`manifest.json` gives the address, chain, year and classes of each contract. The name of a
contract is its page name on the index.
