# Status at a glance (22 November 2026)

A one-page reader's guide: what is proved, what is only tested, what is open. Everything here is
**checked by SIRM** (Lean proofs, Rust tests, Python references, trace replay). A statement is repeated in full, with its limits, in the document it links to.

## What exists

- **Lean 4 specification:** 46 files in `SIRM/`, about 11,800 lines, 430 top-level `theorem` and `lemma`
  declarations, no `sorry` (counted on 22 November 2026 by line-start declarations, so the true number
  of lemmas is higher). `lake build` checks them.
- **Rust reference code:** `rust/sirm-codec`, with 30 integration test files.
- **Python references:** 30 scripts under `scripts/`, each regenerating its committed trace byte for byte.
- **CI:** every pull request runs 19 jobs (Lean build, Rust fmt/clippy/tests, 17 static audits).

## Proved in Lean (for the model, not for the code)

| Claim | Where |
|---|---|
| One shared ledger of eleven operations (including the arbiter's `resolve`) keeps conservation, vault backing, the migration equation, frozen disputed escrows and a non-decreasing clock | `IntegratedLedger` |
| Deny by default; no debit without control; time, filings (creation and removal) and issuance only by explicit grant | `IntegratedLedger` (authorization) |
| With a `u128` ceiling added as one more validation, every counter, burned total and balance stays at most 2^128 - 1; a request that does not fit changes nothing | `BoundedAmounts` |
| An arbiter with an explicit grant can resolve a frozen dispute exactly once; value is neither created nor destroyed; a filing disappears only through such a resolve | `DisputeResolution`, `IntegratedLedger` |
| Request encoding v2 (eleven operations): round trip, injectivity, every accepted byte string is canonical, unknown tag rejected (table agreement with Rust and Python is tested, not proved) | `RequestEncodingV2` |
| Signed request envelope v3: decoder inverts encoder, distinct wires for distinct envelopes, accepted wires canonical, other domains (v2 wire, signing message) rejected, signing message fixes chain, suite, key id and the whole request (signature itself and key registry not modelled) | `SignedEnvelopeV3` |
| State commitment v6, hash left abstract: under a collision-free hash equal roots have equal components, v5 and v6 roots never coincide, a cache entry fixes the cached request (including a `resolve` id and side) and its outcome (the trees and digests are opaque 32-byte values) | `StateCommitmentV6` |
| Cache digest v6: entries carry their own length, so the concatenation is unambiguous; under a collision-free hash the digest determines the list of cached requests and outcomes (sorting by request id and building the list from a machine state are not modelled) | `CacheDigestV6` |
| Escrow and config digests v6: fixed-width entries with a count and flag bytes are unambiguous; under a collision-free hash the digests determine the escrow table (deadlines, records, filings) and the config (shape, vault, deadlines, migration rate, controls, limits, ids including arbiter grants, clock) | `EscrowConfigDigestV6` |
| Sparse Merkle tree (balance, supply, nonce roots): under a collision-free hash with 32-byte outputs, equal depth-64 roots mean the same set of key-value entries (so also the same absent keys); the empty list gives the empty-subtree hash | `SparseTreeV0` |
| Balance, supply and nonce roots: the same root means the same balance for every account and asset in range, the same minted and burned per asset, the same nonce per principal (zero values are absent; same hypotheses; the code enumerating exactly these keys is tested, not proved) | `LedgerRootsV0` |
| **State root v6 as a whole** (`state_root_binds`): under the abstract hash hypotheses (collision free, 32-byte byte outputs), equal roots mean the same shape, clock, migration totals, balances, supplies, nonces, config (arbiter grants included), cache (cached `resolve` requests and outcomes included) and escrow table; the hash is assumed, not proved, and the code building the lists is tested, not proved | `StateRootV6` |

## Checked by tests (differential evidence, not proof)

- Rust against independent Python traces for each ported module, and a seeded fuzz of the processor.
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
- Arbiter resolution is accounted for (Lean pipeline, Rust and Python machines, request v2, signed v3,
  commitment v6), but who the arbiter is, evidence, deadlines, appeals and reversal are open, and nothing
  claims a resolution is fair. The byte layout of the signed envelope has a Lean counterpart (`SignedEnvelopeV3`); the signature check does not; the commitment has a Lean statement of what the root binds (`StateCommitmentV6`), not of how the digests are computed.
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
