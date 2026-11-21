# Status at a glance (21 November 2026)

A one-page reader's guide: what is proved, what is only tested, what is open. Everything here is a
**proposal, not adopted**. A statement is repeated in full, with its limits, in the document it links to.

## What exists

- **Lean 4 specification:** 38 files in `SIRM/`, about 11,300 lines, 322 top-level `theorem` and `lemma`
  declarations, no `sorry` (counted on 21 November 2026 by line-start declarations, so the true number
  of lemmas is higher). `lake build` checks them.
- **Rust reference code:** `rust/sirm-codec`, with 25 integration test files.
- **Python references:** 26 scripts under `scripts/`, each regenerating its committed trace byte for byte.
- **CI:** every pull request runs 19 jobs (Lean build, Rust fmt/clippy/tests, 17 static audits).

## Proved in Lean (for the model, not for the code)

| Claim | Where |
|---|---|
| One shared ledger of eleven operations (including the arbiter's `resolve`) keeps conservation, vault backing, the migration equation, frozen disputed escrows and a non-decreasing clock | `IntegratedLedger` |
| Deny by default; no debit without control; time, filings (creation and removal) and issuance only by explicit grant | `IntegratedLedger` (authorization) |
| With a `u128` ceiling added as one more validation, every counter, burned total and balance stays at most 2^128 - 1; a request that does not fit changes nothing | `BoundedAmounts` |
| An arbiter with an explicit grant can resolve a frozen dispute exactly once; value is neither created nor destroyed | `DisputeResolution` |

## Checked by tests (differential evidence, not proof)

- Rust against independent Python traces for each ported module, and a seeded fuzz of the processor.
- Request encoding v2 has a Lean counterpart (`SIRM/RequestEncodingV2.lean`): round trip, injectivity, and "every accepted byte string is canonical" for all eleven operations; that the Lean table equals the Rust and Python tables is differential evidence only.
- State commitment v6 (v5 plus `resolve`): 402 base and 300 resolve-trace state roots are byte-identical between the independent Python reference and the Rust machine (`rust/sirm-codec/tests/commit_v6_conformance.rs`).
- Signed request v3 (carries request encoding v2): 26 valid vectors and 32 negative cases in Python and Rust, Ed25519 signatures reproduced byte for byte, a signed `resolve` settles a dispute end to end through the Rust machine (`rust/sirm-codec/tests/signed_v3_conformance.rs`); ML-DSA and hybrid wires are still refused in Rust (no verifier chosen).
- Request encoding v2 (v1 plus `resolve`): 19 vectors and both reference traces (27816 and 25137 requests) are reproduced byte for byte by Rust and Python, and every single-byte mutation is rejected or canonical (`rust/sirm-codec/tests/request_v2_conformance.rs`).
- The `u128` ceiling: 400 seeded runs near `u128::MAX` compare the Rust machine with the Lean predicate
  (`rust/sirm-codec/tests/integrated_ceiling.rs`). Writing it found a test-only bug in
  `Machine::invariant()`, fixed in the same change.

## Not done

- No independent cryptographic or protocol review. This is the main open risk; no human reviewer is
  part of the project.
- Nothing proves that the Rust or Python code refines the Lean model.
- Arbiter resolution is a separate Lean layer: not in the request pipeline, the wire formats or the Rust
  and Python machines. Who the arbiter is, evidence, deadlines and appeals are open.
- The clock and ids are unbounded naturals in Lean; wall-clock binding and scheduler liveness are open.
- No deployment, custody, reserves, settlement or regulatory operation of any kind.

## Check it yourself

```
lake build                                  # Lean proofs
cd rust/sirm-codec && cargo test --locked   # Rust tests
python3 scripts/ci_audit.py all             # static audits
```

Reviewers: start with [REVIEWER_GUIDE](REVIEWER_GUIDE.md).

Related: [ROADMAP](ROADMAP.md), [FORMALIZATION_STATUS](FORMALIZATION_STATUS.md),
[TESTING](TESTING.md), [INTEGRATED_STATE_MACHINE_PROPOSAL](INTEGRATED_STATE_MACHINE_PROPOSAL.md).
