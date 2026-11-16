# State commitment v4 (proposal, not adopted)

Status: proposal (phase P4 of `docs/POST_QUANTUM_SECURITY_ARCHITECTURE.md`). It does not replace
v0 to v3. Reference: `scripts/state_commitment_v4_reference.py`. Vectors:
`engineering/canonical_encoding/results/state_commitment_v4_vectors.json`. Rust:
`rust/sirm-codec/src/commit_v4.rs`, tests `rust/sirm-codec/tests/commit_v4_conformance.rs`.
No Lean statements exist for this layer.

## What v4 adds to v3

v3 commits balances, supply, nonces, key registry, suite registry, header, request-id cache,
authorization policy, account/asset registry and the escrow component. v4 keeps all of that and
adds the **asset-migration component** (`SIRM.AssetMigration` and its authorized and
replay-protected variants, at the holdings level).

## Layout

    migration commit = SHA256("SIRM/MIG/v4\0" | accounts u32 | assets u32 | balance root | supply root
                              | source holder u32 | recipient u32 | source asset u32 | dest asset u32
                              | numerator u128 | denominator u128 | total source u128
                              | total target u128 | dust u128
                              | n u32 | n entries (principal u32 | next nonce u64))
                       entries are the principals whose next nonce is not zero, ascending
    state root v4    = SHA256("SIRM/STC/v4\0" | accounts u32 | assets u32 | balance root | supply root
                              | nonce root | key root | header hash | cache | policy | registry
                              | escrow | migration)

The balance and supply roots inside the migration commit are the same sparse trees as in v0, over
the migration machine's own holdings. The stream moves asset 0 into asset 1 in the reference traces.

## Design notes

- As with escrow, the migration machine keeps its own holdings in the current code, so the commit
  carries its own roots. Sharing one ledger across all machines is future integration.
- The exact dust accumulator and both totals are committed, so the equation
  `total_source * numerator = total_target * denominator + dust` is checkable from the committed
  values alone.
- A principal with nonce 0 is not listed; an absent and a zero nonce are the same state.

## Checks

The Python reference commits the final state recorded in the independent migration trace
(1505 episodes), not a state produced by Rust. Rust replays each episode through `Migration` and
the 1505 commitments are byte-identical (all distinct). Twelve single-field changes (holder,
recipient, rate, totals, dust, nonce changed or cleared, balance, minted, burned) each give a
distinct commitment. The full root over the processor sample, one escrow episode and one rich
migration episode (dust carried, several principals with nonces) is identical in both
implementations.

## What is not covered, and why

- **Fees:** the fee port has no persistent state of its own (a fee transfer only moves holdings),
  so there is nothing to commit beyond the holdings already covered.
- **Governance:** there is no governance module in this repository (neither Lean nor Rust), so
  nothing exists to commit yet.
- **Threshold acceptance:** `threshold_accepts` is a stateless check over a request; the key
  records it relies on are part of the key registry from v1.
- The machines (processor, escrow, migration) still have separate ledgers; there is no single
  integrated protocol state, and no inclusion proofs for the list-hash components.

A matching root is differential evidence only, not a refinement proof, and not a commitment to a
complete protocol state, because that state is not yet defined in one place.
