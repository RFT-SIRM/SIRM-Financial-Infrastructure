# Integrated state machine — proposal, nothing implemented

Status: **proposal**. Steps I1 (an independent Python reference with seeded traces,
`scripts/integrated_machine_reference.py`) and I2 (a Rust port with a differential test,
`rust/sirm-codec/src/integrated.rs`) exist; no Lean or encoding change yet. This document records the
design and a staged plan so the work can be checked step by step.

## The problem

The repository has several verified-by-test machines, each with its **own ledger**:

- the integrated processor (transfer, issue, burn; nonces; request-id cache; authorization policy);
- the escrow machine (pooled vault, deadlines, dispute filings);
- the asset-migration machine (exact rate, dust, nonces);
- the key registry (separate from balances).

The state commitments v3 and v4 therefore commit three separate holdings. A transfer cannot
fund an escrow that lives in the same ledger, and a migration cannot burn what the processor
issued. There is no single protocol state, no single operation stream, and nothing a signed request
can address as a whole. The commitment is a composite, not a root of one state.

## Proposed design

1. **One ledger.** A single `Holdings` (balances, supply) shared by every operation.
2. **One request pipeline.** Every state-changing action is a request with principal, nonce and a
   request id, passing through the same replay protection, nonce check, authorization and
   request-id cache as today's transfer, issue and burn.
3. **Operation set.** Today's transfer, issue, burn; plus escrow open, release, cancel, expire,
   dispute; advance time; migrate. Existing tags 0 to 2 keep their meaning; new operations get new
   tags, so existing encodings and vectors stay valid.
4. **Deny by default.** Each new operation needs an explicit grant in the policy for the acting
   principal. No new roles are invented: who may release, cancel, dispute, advance time or migrate
   is whatever the genesis policy grants. (The Lean models say authorization is a separate witness;
   this keeps that.) A designated clock grant covers advancing time.
5. **Atomic.** An operation validates everything before its first write; a rejected request changes
   nothing but the cache entry, as today.
6. **Invariants** to state and test at every step: conservation (minted = burned + sum of balances,
   per asset); the vault holds exactly the pending escrow amounts per asset; the dust equation of
   the migration stream; every filing belongs to a stored record; nonces never decrease; a cached
   response is returned byte-identically for a replay.

## Effect on other layers

- **Request encoding:** a new version with additional operation tags (a proposal, like v0); v0 and v1
  vectors are unaffected.
- **State commitment:** a new version replaces the separate escrow and migration ledgers by the one
  balance and supply root, and commits the escrow table, migration configuration, dust and the
  shared nonces once.
- **Lean:** the generic `SIRM/AuthenticatedStep.lean` wrapper can be instantiated with this machine;
  proving the machine's invariants in Lean is a separate step and is not claimed here.
- **Post-quantum:** no change; signatures stay at the boundary (`PQ_DECISIONS_PROPOSED.md`).

## Plan and gates

| Step | Content | Gate |
|---|---|---|
| I1 | Independent Python reference with seeded traces, committed as JSON | invariants checked at every step |
| I2 | Rust implementation, differential test against I1 | byte-identical outcomes and final states |
| I3 | Request encoding with new operation tags | round trip and mutation tests |
| I4 | State commitment for the one-ledger state | Python and Rust agree |
| I5 | Lean statements for the invariants | built in CI; stated assumptions |

Each step ends in its own pull request and is labelled proposal until the architecture has had
independent review (no reviewer exists yet; this is the main open risk).

## What this does not do

It does not change anything that is adopted, it does not prove the new machine correct (I1 and I2
are differential evidence, not a refinement proof), and it does not decide governance or fee
policy. Fees have no persistent state, and there is no governance module.

## Step I1 result (Python reference)

`scripts/integrated_machine_reference.py` implements the design with one shared ledger and the
pipeline above, and writes `engineering/ledger_core/results/integrated_trace_v0.json` (402 episodes:
2 hand-built at the u128 boundary, 400 seeded). Results:

- **Backward compatible:** with escrow, migration and the new grants unused, it reproduces the 4000
  tokens, final balances, supply, nonces and receipt count of the old processor trace byte for byte.
- **Invariants at every step:** conservation per asset; vault balance equals the pending escrow
  amounts per asset; the dust equation; every filing belongs to a stored record; and a rejected,
  replayed, conflicting, stale or future request changes none of the ledger, nonces, records,
  filings or clock.
- **Coverage:** all ten operations have at least 30 accepted cases each (the script asserts this),
  the denial classes of every operation occur, and the u128 boundary denials are present.
- **Reserved vault:** transfer, issue to it and burn from it are rejected. This rule is new and is
  needed for the vault invariant; it is a design choice, not taken from the Lean models.
- Credit overflow in escrow settlement cannot occur because every balance is bounded by the supply
  and issue is rejected before the supply passes 2^128 - 1.

This is a reference, not a proof: the rules for the new operations (who is authorized, what is
denied) are defined here and have no Lean counterpart yet.

## Step I2 result (Rust port)

`rust/sirm-codec/src/integrated.rs` ports the reference; `rust/sirm-codec/tests/integrated_trace.rs`
replays all 402 episodes of `integrated_trace_v0.json` and checks every outcome token, the final
balances, supply, nonces, clock, receipt count, escrow records, dispute filings and migration totals;
after every step the Rust invariants hold (conservation, vault equals pending escrow, dust equation,
filings imply records) and every rejected request leaves the state unchanged. The old integrated
processor trace (4000 requests) replayed through the new machine gives the same tokens and final
state. This is differential evidence on seeded traces, not a refinement proof.

The comparison found two defects in the reference itself, both fixed: the code `dispute:a` meant
both "authorization denied" and "already filed" (authorization is now `<op>:auth`), and the trace
generator produced replayed requests with an extra argument that no typed request can express (it now
mutates the last argument instead).

Step I3 (request encoding v1, `engineering/canonical_encoding/SPEC_request_v1.md`): all 10 operations have a canonical encoding with an independent Python reference and a Rust codec; the Rust side reproduces the vectors and the digest over 27816 trace requests, accepts only canonical inputs, and replays decoded requests through the machine with identical outcomes. Request ids are now 32 bytes in the Rust machine. Signed requests v0 and v1 embed only v0 request bytes; signed request v2 carries request v1.

Step I4 (state commitment v5, `engineering/canonical_encoding/SPEC_state_commitment_v5.md`): one root over the shared ledger, nonces, configuration (policy, deadlines, vault, migration rate), request cache (full request v1 bytes plus outcome), escrow table and migration totals. Independent Python reference over the final states of the 402 episodes; Rust reproduces all 402 roots byte for byte.

Step I5 (partial, `SIRM/IntegratedPipeline.lean`): a generic Lean model of the request pipeline, no Mathlib, built in CI and also checked locally with Lean 4.33.1. Proved for any core state and any authorization, validation and effect functions: a cached identical request is answered from the cache and changes nothing (replay), a different request under the same id is a conflict, stale and future nonces change nothing and are not cached, an unauthorized request is denied with the authorization denial whatever validation would say, a denial changes neither core nor nonces and is cached, an accepted request advances only the sender's nonce by one, receipts are never overwritten, nonces never decrease, any invariant preserved by accepted effects is an invariant of the whole pipeline, replaying a processed request returns the same receipt, and an accepted request under a new id is stale. Only the axioms `propext` and `Quot.sound` are used. Not proved: the concrete ledger invariants (supply conservation, vault backing, the migration equation) over the real operations, and that the Rust and Python machines implement this model (that evidence is differential testing).

Signed request v2 (`engineering/canonical_encoding/SPEC_signed_request_v2.md`): wire, signing message and verification order of v1 carrying request encoding v1 (all ten operations, 32-byte request id). Python reference with frozen ML-DSA, hybrid and Ed25519 vectors; Rust verifies the Ed25519 suite (signatures reproduced byte for byte) and refuses ML-DSA and hybrid wires with `VerifierUnavailable` after all structural checks (no post-quantum verifier chosen); end to end into `integrated::Machine`.

Step I5 (concrete slice, `SIRM/IntegratedLedger.lean`): a concrete core state (one shared ledger, supply counters, escrow records, a reserved vault account) with transfer, issue, burn, open, release, cancel, expire and migrate, instantiated into the generic pipeline. Proved by induction over the pipeline, for any authorization function and any validation that implies the ledger preconditions: for every asset `minted = burned + sum of all balances` (conservation); the vault balance equals the sum of the pending escrows of that asset (vault backing); escrow accounts are real accounts and never the vault; and the migration equation `total source * num = total target * den + dust` with `dust < den` (migrate is the proved burn followed by the proved issue plus the carried remainder). 28 theorems, only `propext` and `Quot.sound`, no Mathlib, compiled locally with Lean 4.33.1 and by CI. Amounts are natural numbers, so the `u128` overflow denials are not modelled (they only add denials); time, deadlines, disputes (filings) and the clock are not in this slice; the real validation is stricter than the stated preconditions. Nothing connects the model to the Rust and Python machines except the shape of the operations.

Not yet done: disputes, time and deadlines in the Lean core, the key, suite and registry parts in the integrated root. The existing escrow and migration ports (own ledgers) and commitments v3 and v4
remain as they are until I4 replaces them.
