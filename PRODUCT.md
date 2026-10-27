# Product

<!-- impeccable:product-schema 1 -->

## Platform

web

## Users

Four confirmed audiences share one surface, in this order of weight:

- Security auditors reading one contract deeply for an hour at a desk, on a large monitor, with the decompiled code, the security report and the storage layout open together.
- Developers running a pre-deployment check: they paste freshly compiled bytecode and want a verdict and the risky lines fast.
- Researchers and CTF players working through many addresses quickly, comparing functions and copying code out constantly.
- A mixed public audience on a hosted instance, from curious users to auditors, including people on phones.

## Product Purpose

evmdec turns any EVM contract, fetched by address on any EVM chain or pasted as creation or runtime bytecode, into structured, readable pseudo-Solidity, and analyses it for security defects with evidence. Success is a reader who understands what a contract really does and where it is dangerous, without the source.

## Positioning

A from-scratch Rust decompiler whose lifted semantics are verified block by block against a concrete EVM interpreter on random inputs, and whose analyzer's recall is measured on a corpus of 24 publicly exploited contracts (23/23 detectable found) while its false-positive load is measured on 22 audited mainnet contracts. The numbers are published and reproducible; competitors ship decompilers without them.

## Operating Context

- Input is an address plus chain, or raw bytecode hex; proxies are followed to their implementation and both are shown.
- Output per contract: pseudo-Solidity source with recovered functions (selectors, parameters, mutability, returns), internal functions, storage layout (including packed fields), events, custom errors, revert strings, selectors called on other contracts; a markdown security report with findings carrying severity, confidence, function, program counter, evidence lines and a recommendation, a risk score 0 to 100, privileged functions and state-changing functions callable by anyone; the disassembly; the JSON of everything; a downloadable `.sol`.
- The web app is an axum server serving one static page (`crates/server/static/index.html`) over `/api/decompile`, `/api/address/{chain}/{address}` and `/api/chains`. A decompile takes tens to hundreds of milliseconds.
- The same output is produced by the CLI (`evmdec decompile|analyze|verify|disasm|info|cfg`); the web UI is the shared, linkable face of it.

## Capabilities and Constraints

- Any bytecode decompiles; unresolved jumps and uncovered blocks are reported as numbers, never hidden.
- Function names come from a built-in signature dictionary or an optional online lookup; unknown functions are `func_<selector>`, unknown events `Event_<topic prefix>`.
- The report is heuristic: findings are leads with a confidence level, and the UI must present severity and confidence together, never severity alone.
- The current page has no routing: a result is not linkable. Shareable links (chain + address in the URL) are a confirmed requirement of the hosted deployment.
- Terminology to keep: selector, external/internal function, storage slot, finding, severity (Critical/High/Medium/Low/Info), confidence, risk score, coverage, unresolved jumps, proxy/implementation.
- Undecided: whether the hosted instance adds rate limiting or history; not part of this redesign.

## Brand Commitments

- Name: `evmdec`, lowercase, set as one word. No logo exists; none is to be invented beyond the wordmark.
- Voice: plain, precise, no hype; numbers are stated with what they do not cover (see README's Accuracy section).

## Evidence on Hand

- Real decompilations and reports for 22 audited mainnet contracts (`testdata/mainnet`) and 24 exploited contracts (`testdata/vuln`), usable as demonstration content without fabrication.
- Measured results in README.md and docs/verification.md (interface recovery, oracle mismatches, random-sample run, analyzer recall).
- No testimonials, customers, pricing or endorsements exist; none may be invented.

## Product Principles

1. The contract is the content: code, findings and layout are shown at reading quality, and the interface stays out of the way.
2. Evidence before verdict: every finding links to the line it is about; a score is never shown without what produced it.
3. Honest numbers: coverage, unresolved jumps, confidence and what was not analysed are always visible.
4. One tool for four readers: the deep-reading auditor and the phone-holding visitor use the same surface, which adapts structurally rather than hiding things.
5. Fast and self-contained: no third-party scripts on the hosted page (the three typefaces load from Google Fonts with system fallbacks, nothing else is external); a result renders in the time the decompiler takes.

## Accessibility & Inclusion

- WCAG 2.2 AA is required: contrast (1.4.3, 1.4.11), focus visible and not obscured (2.4.7, 2.4.11), focus appearance, target size minimum 24x24 (2.5.8), dragging not required (2.5.7), consistent help, redundant entry, and accessible authentication do not apply or are met by design.
- Light and dark color schemes, following the system setting with a manual override, each meeting AA contrast including the code highlighting and severity colors.
- Full keyboard operation with visible focus, landmarks, headings in order, status messages announced via live regions, and reduced-motion respected.
- Severity is never conveyed by color alone: a label or icon accompanies it.
