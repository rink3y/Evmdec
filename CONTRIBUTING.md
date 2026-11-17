# Contributing

## Before you push

```sh
cargo fmt --all
cargo clippy --workspace --all-targets --all-features
cargo test --workspace
python3 corpus/bench.py
RUNS=8 ./corpus/verify_all.sh
```

Clippy is kept at zero warnings. `bench.py` measures interface recovery on the audited corpus
and `verify_all.sh` runs the block oracle, where every block must agree with the interpreter.
The numbers those print are the ones in the README. A change that moves them has to say so.

## The analyzer

The analyzer in `crates/audit` reports consequences a run showed. It has no rules that match
code, and a change must not add one.

- Nothing in it names a contract, a protocol, a token, a standard or an address. Function
  selectors appear in one place only, `world.rs`, where the local world speaks the asset
  interface the same way it moves ether. They never decide a finding.
- A fix is for a general cause. If it only helps the contract it was found on, it is not a
  fix. Say in the commit which unrelated contracts it also changes.
- A finding is built on a run and carries the steps to make that run again. A doubt about a
  finding becomes a second test that re-runs it, not a filter on its shape.
- A false finding on a contract with no known flaw is traced to what the world or the law
  got wrong, and that is corrected. The contract is not exempted.
- New logic gets one small test: a unit test beside it, or a source fixture in
  `testdata/source` with the flawed contract and the sound one closest to it.
- `testdata/heldout` is never read and never tuned on. It is scored by reviewers who return
  counts only.

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
