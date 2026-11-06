# Contributing

## Before you push

```sh
cargo fmt --all
cargo clippy --workspace --all-targets --all-features   # zero warnings
cargo test --workspace
python3 corpus/bench.py        # interface recovery on the audited corpus
python3 corpus/vuln_bench.py   # recall on known exploits and the false-positive budget
RUNS=8 ./corpus/verify_all.sh  # block oracle: every block must agree with the interpreter
```

The numbers those print are the ones in the README. A change that moves them has to say so.

## Rules

Analyzer rules are written in bytecode facts: widths, uses, storage shapes, call targets,
comparisons. A rule never names a contract, a protocol, a token or an address. If a rule needs
a list of selectors, the list is secondary evidence and the rule must still fire without it.

Every rule carries a test on hand-assembled bytecode in `crates/decompiler/tests/analyzer.rs`,
with a positive case and the nearest legitimate pattern as a negative case.

## Style

Google's Rust style guide, `rustfmt.toml` as committed, `#![warn(missing_docs)]`: every item
has a doc comment. Named-field structs over tuples of more than two elements. No `allow`
attributes without a reason in the same line.

## Commits

One change per commit. The message says what moved and why, not how. No sign-offs, no
trailers, no tool attributions.
