# State commitment v5 (proposal, not adopted)

One commitment for the integrated state machine (`docs/INTEGRATED_STATE_MACHINE_PROPOSAL.md`, step I4):
a single shared ledger, one nonce table, one request cache, one escrow table. It replaces the separate
escrow and migration ledgers of v3 and v4 for the integrated machine; v0 to v4 stay as they are.
Reference: `scripts/state_commitment_v5_reference.py`. Vectors:
`results/state_commitment_v5_vectors.json`. Rust: `rust/sirm-codec/src/commit_v5.rs`, test
`rust/sirm-codec/tests/commit_v5_conformance.rs`. No Lean statements exist for this layer.

## Layout (big-endian)

    state root v5 = SHA256("SIRM/STC/v5\0" | accounts u32 | assets u32 | balance root | supply root
                           | nonce root | config | cache | escrow | now u64
                           | total source u128 | total target u128 | dust u128)
    config  = SHA256("SIRM/CFG/v5\0" | accounts u32 | assets u32 | vault flag u8 + u32
                     | n u32 + n deadlines u64
                     | migration flag u8 + holder u32 + recipient u32 + source u32 + destination u32
                       + numerator u128 + denominator u128   (49 zero bytes if absent)
                     | controls | limits | ids | clock)
    each policy list = n u32 + entries sorted bytewise:
      control (principal u32, account u32)
      limit   (principal u32, tag u8, a u32, b flag u8 + b u32, asset u32, limit u128)
      id      (principal u32, tag u8, id u32)
      clock   (principal u32)
    cache   = SHA256("SIRM/CAC/v5\0" | n u32 | entries by request id)
      entry  = request encoding v1 (request id included) | stored outcome (11 bytes)
      stored = flag u8 (1 accepted, 2 denied) | kind tag u8 | cause u8 | nonce u64
               accepted: nonce consumed, kind and cause 0; denied: kind tag, cause code, expected nonce
      cause codes: auth 0, reserved 1, vault-or-overflow 2, frozen 3, unknown id 4, id in use 5,
                   not pending 6, deadline passed 7, deadline not reached 8, zero amount 9,
                   unknown account 10, insufficient 11, time not forward 12, already filed 13,
                   claimant not party 14
    escrow  = SHA256("SIRM/ESC/v5\0" | n u32 | n id entries)   (id entry as in v3, 55 bytes)

Balance, supply and nonce roots are the sparse trees of v0. The escrow vault is an ordinary account of
the shared ledger, so its balance is inside the balance root. The migration totals are 48 zero bytes
when no stream is configured. Operation tags are those of request encoding v1.

## Design notes

- The cache holds the full request, so a replay or conflict decision is checkable from the committed
  bytes. Reusing request encoding v1 for the entries means one encoding for requests everywhere.
- The configuration (policy, deadlines, vault, migration rate) is committed separately from the mutable
  state, so a verifier can check that two roots were produced under the same rules.
- A cached request whose escrow id does not fit in u32 cannot be encoded; the root is then undefined
  (`None` in Rust). The machine itself accepts any `usize` id; a deployment must bound ids to u32.

## Checks

The Python reference commits the final model state of the 402 integrated episodes, regenerated from
its seed and compared with the committed trace (not a state produced by Rust). Rust replays each
episode through `integrated::Machine`; all 402 roots are byte-identical (and pairwise distinct), and so
is their aggregate digest. Components (balance, supply, nonce roots, config, cache, escrow) of a rich
example (filing, settled record, dust, several principals) agree. Seventeen single-field changes
(balance, minted, nonce, time, dust, both totals, a limit, a control grant, the clock grant, the vault,
a deadline, the migration rate, a filing, a record phase, a cached outcome, a removed cache entry) each
give a distinct root in Python. In Rust every request that changes state or is cached changes the root,
and stale, future or replayed requests leave it unchanged.

## Not covered

Key registry, suite registry, header, account and asset registry (v1 and v2 parts), fee parameters,
governance (no module exists), inclusion proofs for the list-hash parts. Proposal only; differential
evidence, not a proof.
