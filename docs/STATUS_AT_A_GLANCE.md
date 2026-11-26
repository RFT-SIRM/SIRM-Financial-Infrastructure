# Status at a glance (25 November 2026)

A build report: which floors stand, what holds each one up and what was run to check it. Every line says what checked
it: Lean proofs, Rust tests, Python references, trace replay, CI, or the review of 25 November 2026
([REVIEW_2026-11-25](REVIEW_2026-11-25.md)). A statement is repeated in full, with its limits, in the document it
links to.

## What stands

| Floor | What is built | Checked by |
|---|---|---|
| 1. Specification | Lean 4: 47 files in `SIRM/`, about 13,805 lines, 456 top-level `theorem` and `lemma` declarations (counted on 25 November 2026 by line-start declarations), no `sorry` | `lake build`, `lake test`, the CI audit "No proof placeholders", an axiom scan of every theorem (CI step) |
| 2. Proved decision core | `rust/sirm-keys-core`: key distinctness, threshold, nonce class, nonce successor, migration arithmetic, checked `u128` sums and differences. Ten specifications are proved for its Aeneas translation, with only the axioms `propext`, `Classical.choice`, `Quot.sound` | CI job `Refinement / build and proofs` (`lake build`, `refinement/check_proofs.sh`) |
| 3. Reference machine | `rust/sirm-codec`: eleven operations behind one pipeline (`integrated::Machine`). It takes its nonce decision, checked sums and differences, migration arithmetic and the four balance checks from the proved core | Rust against independent Python traces, seeded fuzz, adversarial stress test (CI: 180,000 requests; extended run: 9 million) |
| 4. Wire layer | Request encoding v2, signed request v3 (Ed25519 with strict verification; ML-DSA and hybrid wires are refused, no verifier chosen), state commitment v6 | The 15 committed vector files are reproduced byte for byte by the Python references; Rust conformance tests; signature stress test (CI: 125,000 bit flips; extended run: 2.5 million) |
| 5. Gate | 20 required checks on `main` | Lean build and tests, Rust fmt, clippy and tests, Refinement build, 17 static audits |

## Review of 25 November 2026

Reviewer: Claude, the AI that wrote most of this code (so not a third-party audit). Run: build, fmt, clippy, all
125 Rust tests, the 29 Python references (the 15 committed vector files reproduced byte for byte), the locked
dependencies against the RustSec advisories. Read: the signature verification in full, the machine pipeline and
validation, the decoders, the commitment framing. Stress: 9 million hostile requests against the machine and 2.5
million single-bit flips against signed wires, nothing accepted that should not be, no panic, invariants intact.
Found: no defect in the checked code; one open design point (the response cache has no bound), three notes, one test
gap closed. Full list with numbers and what was not covered: [REVIEW_2026-11-25](REVIEW_2026-11-25.md).

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
| **Wire bytes to the machine in one theorem** (`wire_processed`, `wirePipeline_rejected_untouched`, `wirePipeline_nonces_le`): a byte string that reached the machine decoded to a canonical v3 envelope for this chain, its principal is registered under the claimed suite, the suite is permitted and the abstract verifier accepted the signature over the signing message, which binds chain, suite, key id and the whole request; malformed, wrong-chain or unauthenticated bytes leave the state untouched; no stored nonce exceeds the ceiling after any byte string; the verifier is assumed, not proved | `SignedPipelineV3` |

## Checked by tests (differential evidence, not proof)

- Rust against independent Python traces for each ported module, and a seeded fuzz of the processor.
- State commitment v6 (v5 plus `resolve`): 402 base and 300 resolve-trace state roots are byte-identical between the independent Python reference and the Rust machine (`rust/sirm-codec/tests/commit_v6_conformance.rs`).
- Signed request v3 (carries request encoding v2): 26 valid vectors and 32 negative cases in Python and Rust, Ed25519 signatures reproduced byte for byte, a signed `resolve` settles a dispute end to end through the Rust machine (`rust/sirm-codec/tests/signed_v3_conformance.rs`); ML-DSA and hybrid wires are still refused in Rust (no verifier chosen).
- Request encoding v2 (v1 plus `resolve`): 19 vectors and both reference traces (27816 and 25137 requests) are reproduced byte for byte by Rust and Python, and every single-byte mutation is rejected or canonical (`rust/sirm-codec/tests/request_v2_conformance.rs`).
- The `u128` ceiling: 400 seeded runs near `u128::MAX` compare the Rust machine with the Lean predicate
  (`rust/sirm-codec/tests/integrated_ceiling.rs`). Writing it found a test-only bug in
  `Machine::invariant()`, fixed in the same change.
- Adversarial stress test of the machine (`rust/sirm-codec/tests/integrated_fuzz.rs`): hostile requests (boundary amounts, out-of-range accounts and ids, stale, future and maximal nonces, repeated request ids); after every request no panic, the machine invariant holds, a non-executing outcome changes nothing, an accepted request advances exactly one nonce. Four deliberate faults put into a copy of the code were all caught.
- Signature-layer stress test (`rust/sirm-codec/tests/signed_fuzz.rs`): every single-bit flip, truncation and extension of valid signed wires is rejected, as is a non-canonical scalar `S + L`; a universal forgery under a weak key is rejected; random bytes never panic the verifier or the decoder, and whatever the decoder accepts re-encodes to the same bytes; the key registry rejects malformed keys.

## Boundaries

- The Rust and Python code is tied to the Lean model by the proved decision core and by tests everywhere else; the
  machine as a whole is not proved to refine the model.
- Signatures: Ed25519 is verified; ML-DSA and the hybrid suite have no verifier chosen. The Lean envelope and commitment
  statements assume an abstract verifier and an abstract collision-free hash.
- Arbiter resolution is accounted for end to end (Lean pipeline, Rust and Python machines, request v2, signed v3,
  commitment v6); who the arbiter is, evidence, deadlines, appeals and reversal are open.
- The clock and ids are unbounded naturals in Lean; wall-clock binding and scheduler liveness are open. The response
  cache has no bound (finding F3 of the review).
- Not in this repository: deployment, custody, reserves, settlement and regulatory operation.
- Release gates B and D ask for an independent audit; the review above is by the author-side tool and does not replace it.

## Check it yourself

```
lake build                                  # Lean proofs
cd rust/sirm-codec && cargo test --locked   # Rust tests, including the stress tests
python3 scripts/ci_audit.py all             # static audits
```

Reviewers: start with [REVIEWER_GUIDE](REVIEWER_GUIDE.md).

Related: [ROADMAP](ROADMAP.md), [FORMALIZATION_STATUS](FORMALIZATION_STATUS.md),
[TESTING](TESTING.md), [INTEGRATED_STATE_MACHINE_PROPOSAL](INTEGRATED_STATE_MACHINE_PROPOSAL.md),
[REVIEW_2026-11-25](REVIEW_2026-11-25.md).
