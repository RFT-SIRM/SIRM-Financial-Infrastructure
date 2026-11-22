# State commitment v6 (checked by SIRM)

State commitment v5 for the integrated state machine (`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`) with
the arbiter operation `resolve`. v0 to v5 stay as they are; v5 still has no root for a machine whose cache
holds a `resolve` request. Reference: `scripts/state_commitment_v6_reference.py`. Vectors:
`results/state_commitment_v6_vectors.json`. Rust: `rust/sirm-codec/src/commit_v6.rs`, test
`rust/sirm-codec/tests/commit_v6_conformance.rs`. Lean: `SIRM/StateCommitmentV6.lean` (what the root binds, with the hash left abstract).

## What changes against v5

Only these (a domain tag has one meaning forever):

    state   "SIRM/STC/v6\0"     config  "SIRM/CFG/v6\0"     cache  "SIRM/CAC/v6\0"     escrow  "SIRM/ESC/v6\0"
    cache entry = request encoding v2 (request id included) | stored outcome (11 bytes)
    kind tag 10 (resolve) and cause code 15 (not disputed) are in use

Everything else is as in v5 (`SPEC_state_commitment_v5.md`): the layout of the state root, the config and
policy lists (an arbiter grant is the id entry `(principal, tag 10, id)`), the escrow table with filings,
the balance, supply and nonce trees, the migration totals. A cached `resolve` request is encoded with
request encoding v2 (tag 10, escrow id u32, one flag byte), so the commitment binds its escrow id and its
side (beneficiary or depositor) and its stored outcome (accepted, or denied with the cause code, including
`resolve:o`, code 15). As in v5, a cached request whose escrow id does not fit in `u32` has no root
(`None` in Rust).

## Checks

The Python reference commits the final model state of two trace families, each regenerated from its
seed and compared with the committed trace (not a state produced by Rust): the 402 episodes of
`integrated_trace_v0.json` and the 300 episodes of `integrated_resolve_trace_v0.json`. Rust replays each
episode through `integrated::Machine`; all 402 and all 300 roots are byte-identical to Python (and
pairwise distinct inside each family), and so are their aggregate digests. The components (balance,
supply, nonce roots, config, cache, escrow) of a rich example of each family agree. In Python, seventeen
single-field changes of each example give distinct roots (for the resolve example, 15 of the v5 changes
plus two that alter the cached `resolve` request: its side and its escrow id; the example has no live
filing, so the filing and record-phase variants are exercised by the base example). In Rust every
request that changes state or is cached changes the root (the first 40 resolve episodes are checked
request by request), a denied `resolve` changes only the cache and not the ledger, records, filings,
clock or migration totals, and stale, future or replayed requests leave the root unchanged.

## Not covered

Key registry, suite registry, header, account and asset registry (v1 and v2 parts), fee parameters,
governance (no module exists), inclusion proofs for the list-hash parts. Proposal only; differential
evidence, not a proof.
