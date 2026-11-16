# State commitment v3 (proposal, not adopted)

Status: proposal (phase P4 of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`). It does not replace
v0, v1 or v2. Reference: `scripts/state_commitment_v3_reference.py`. Vectors:
`engineering/canonical_encoding/results/state_commitment_v3_vectors.json`. Rust:
`rust/sirm-codec/src/commit_v3.rs`, tests `rust/sirm-codec/tests/commit_v3_conformance.rs`.
No Lean statements exist for this layer.

## What v3 adds to v2

v2 commits balances, supply, nonces, key registry, suite registry, header, request-id cache,
authorization policy and account/asset registry. v3 keeps all of that and adds the **escrow
component**: the pooled-vault escrow with deadlines (`SIRM.EscrowTimeLocks`) and dispute filings
(`SIRM.EscrowDisputes`).

## Layout

    id entry      = deadline u64 | record flag u8 | depositor u32 | beneficiary u32 | asset u32
                    | amount u128 | phase u8 | filing flag u8 | principal u32 | claimant u32
                    | filed at u64                                   (55 bytes)
                    phase: 1 pending, 2 released, 3 cancelled, 4 expired
                    an absent record or filing is its flag byte 0 followed by zero fill
    escrow commit = SHA256("SIRM/ESC/v3\0" | accounts u32 | assets u32 | balance root | supply root
                           | vault u32 | now u64 | ids u32 | id entries in id order)
    state root v3 = SHA256("SIRM/STC/v3\0" | accounts u32 | assets u32 | balance root | supply root
                           | nonce root | key root | header hash | cache | policy | registry | escrow)

The balance and supply roots inside the escrow commit are the same sparse trees as in v0, over the
escrow machine's own holdings.

## Design notes

- In the current code the escrow machine keeps its own holdings, separate from the integrated
  processor's. v3 therefore commits the escrow state together with its own balance and supply
  roots. A single shared ledger for both is future integration and is not modelled.
- The deadline schedule is fixed in advance per id, so every id has an entry whether or not a
  record exists; the table has a fixed width per id.
- Filings are permanent in the model, so a filing entry never disappears from the committed state
  while the record exists.
- Like the v2 components, this is an ordered list hash: no inclusion proofs.

## Checks

The Python reference regenerates the 1500 episodes of the independent dispute reference from its
seed, checks them against the committed trace, and commits the final state of each. Rust replays
each episode through `DisputedEscrow` and the 1500 commitments are byte-identical (all 1500 are
distinct). Eleven single-field changes (vault, clock, deadline, balance, record amount, phase and
beneficiary, record removed, filing removed, claimant and time) each give a distinct commitment.
The full root over the processor sample plus one rich episode (185: a filing and settled records)
is identical in both implementations. The derived supply (issued units) is cross-checked
against the Python balances.

## Still not covered

Fee parameters, governance state, migration and residual state, threshold policies. This is not a
commitment to the complete protocol state, and a matching root is differential evidence only, not a
refinement proof.
