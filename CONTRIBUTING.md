# Contributing

## Before you push

```sh
cargo fmt --all
cargo clippy --workspace --all-targets --all-features
cargo test --workspace
python3 corpus/bench.py
python3 corpus/vuln_bench.py
python3 corpus/rule_bench.py
RUNS=8 ./corpus/verify_all.sh
```

Clippy is kept at zero warnings. `bench.py` measures interface recovery on the audited corpus,
`vuln_bench.py` recall on known exploits and the false-positive budget, and `verify_all.sh`
runs the block oracle, where every block must agree with the interpreter. The numbers those
print are the ones in the README. A change that moves them has to say so.

## Rules

Analyzer rules are written in bytecode facts: widths, uses, storage shapes, call targets,
comparisons. A rule never names a contract, a protocol, a token or an address. If a rule needs
a list of selectors, the list is secondary evidence and the rule must still fire without it.

Every rule carries a test on hand-assembled bytecode in `crates/decompiler/tests/analyzer.rs`,
with a positive case and the nearest legitimate pattern as a negative case.

A rule that works by running the code also gets a row in `cases()` in the same file: a flawed
fixture and the sound one closest to it. Two tests read that table. One scores it per rule and
fails on any miss or false alarm. The other rebuilds every fixture with a push and a pop after
each jump destination and fails if a result changes, so a rule cannot depend on where the code
happens to sit. `EVMDEC_WRITE_FIXTURES=testdata/rules cargo test the_labelled` rewrites the
fixtures on disk that `corpus/rule_bench.py` scores.

A check that runs code reports only what a run showed. An input the solver produced is run
again on the bytecode before a finding is built on it, and a finding that chose storage to get
a run says so. Standard interfaces are measured, never assumed: a selector says what a function
is called, not what it does.

## Style

Google's Rust style guide, `rustfmt.toml` as committed. Named-field structs over tuples of more
than two elements. An `allow` attribute states its `reason` inside the attribute.

## Comments

As few as possible. Names and structure say what the code does, so a comment never does.

- A comment may only say why: the reason behind a choice, a warning about something that could
  break, or a workaround or a line that looks wrong and is there on purpose.
- If a comment would not stop a future mistake, it is deleted.
- No documentation comments on functions, types or files. Text a program shows its user, such
  as command-line help, goes in an attribute or a string, not in a doc comment.
- Short plain sentences, the way a developer jots them down. No semicolons: two sentences.
- Config files carry no comments between settings. Each section gets one block above it: a
  dashed line, the section name and what it is for, one aligned line per setting, a dashed line.

## Commits

One change per commit. The message says what moved and why, not how. No sign-offs, no
trailers, no tool attributions.
