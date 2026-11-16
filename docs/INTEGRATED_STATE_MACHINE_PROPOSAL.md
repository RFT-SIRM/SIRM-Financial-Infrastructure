# Integrated state machine — proposal, nothing implemented

Status: **proposal**. No code, Lean file or encoding changes with this document. It records a
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
