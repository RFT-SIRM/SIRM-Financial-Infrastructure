# Formalization Status

This file separates Lean declarations present in source from protocol properties still awaiting formalization. A declaration is not described as kernel-checked until the pinned `lake build SIRM` succeeds for the relevant commit.

## Present in the repository

- Supply-state definition and initial-state invariant.
- Mint transition and invariant-preservation theorem.
- Burn transition with an explicit sufficient-outstanding precondition and invariant-preservation theorem.
- Exact 1.309% founder-rate representation as 13,090 ppm.
- Founder allocation floor formula, allocation upper-bound theorem, and founder-plus-remainder equality.
- Genesis allocation record with all non-founder pools explicitly unallocated.
- Generic finite-account, per-asset signed general-ledger model.
- Per-asset balance-conservation theorem for any journal entry carrying its balance proof.
- A balanced transfer-journal constructor for the signed general-ledger view.
- Per-asset holder holdings indexed by account and asset.
- A reconciliation invariant requiring nonnegative holder balances whose total equals outstanding supply.
- A theorem bounding each nonnegative holder balance by total holdings.
- A funded holder-transfer transition preserving balances, nonnegativity and supply reconciliation; self-transfer is a no-op.
- An issuance-to-holder transition that increases the holder balance and outstanding supply equally.
- A burn-from-holder transition bounded by that holder's balance, with a proof that this bound also protects aggregate outstanding supply.
- Proof-carrying transfer and holder-burn transitions: numeric preconditions are explicit proof arguments, so invalid requests have no admissible transition term; every resulting state preserves the holdings invariant.
- Generic reachable-state invariant theorem for a state machine whose initial and transition safety obligations are supplied.
- A dedicated `SIRMTests` Lake test-driver library covering a reconciled two-asset example, funded transfer, overspending rejection, self-transfer, issuance, holder burn, founder allocation arithmetic and journal conservation.

## Not yet formalized

- A canonical typed asset registry with decimals, precision, issuer, status, network identifier and migration rules.
- Account metadata, ownership, account classes, authorization keys and account lifecycle.
- Authorization of issuance, burn permissions, freeze/closure rules and signer thresholds.
- A canonical finite account universe and concrete genesis assignment covering founder, treasury, validator, ecosystem, community and unallocated pools.
- A unified transaction object with signer rules, nonce, expiry, replay prevention, fees and atomic failure semantics.
- A complete link between holder movements and signed general-ledger journal postings, including custody and customer-liability accounting.
- Freeze, escrow, fees, settlement, reversals, credit lines and account restrictions.
- Multi-asset FX, valuation and rounding-residual policies.
- Redemption obligations and their legal/operational preconditions.
- Reserve evidence and external attestations as explicit assumptions with freshness and provenance.
- Governance, validator-set changes, upgrades, rollback and recovery transitions.
- The correspondence between Lean definitions and Rust code.
- Consensus safety, liveness, data availability and privacy proofs.

## Test execution

The pinned workflow explicitly invokes `lake build` and `lake test`. The test driver is a Lean library whose concrete theorem scenarios must compile; it is not a randomized runtime/fuzz harness. Linting is explicitly disabled until a linter driver is configured.

## Assurance rule

No theorem is described as proving more than its exact statement. The holder-supply invariant assumes that the account universe is complete and that each outstanding unit is assigned to exactly one holder/control account. It does not prove legal ownership, private-key custody or external reserves. A later implementation must have a refinement argument; ordinary tests alone do not establish full correspondence.
