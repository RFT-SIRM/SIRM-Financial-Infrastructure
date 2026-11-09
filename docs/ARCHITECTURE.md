# Architecture

## Core rule

The Lean specification is the normative mathematical definition of the protocol. Implementations must be shown to refine this specification; passing tests alone is not a proof of refinement.

## Layers

1. **Formal protocol (Lean 4):** state types, allowed transitions, invariants, authorization rules, and proofs.
2. **Reference implementation (Rust):** deterministic execution of the specified transitions.
3. **Ledger:** ordered, durable records of accepted transitions.
4. **Networking and consensus:** replication, ordering, finality, validator admission, and recovery.
5. **Institutional interfaces:** governance, reserves, settlement, reporting, custody integrations, and compliance controls.

These layers are intentionally separate. The protocol must not depend on a particular chain, token standard, cloud provider, or jurisdiction.

## Initial module boundaries

- Supply accounting: issuance, burn, and outstanding supply.
- Allocation arithmetic: exact integer splits and explicit remainders.
- Accounts: participant identity, balances, and authorization (future).
- Transfers: ownership changes that conserve aggregate supply (future).
- Reserves and liabilities: typed assets, obligations, valuation sources, and haircuts (future).
- Governance: roles, thresholds, timelocks, emergency powers, and bounded upgrades (future).

## Native ledger decision

A native ledger is a future target, not an initial assumption. Before selecting consensus or networking, the project must specify transaction semantics, deterministic state transitions, failure model, data availability, finality, validator incentives, and recovery from conflicting or unavailable state.

## Compatibility with previous prototypes

Rift-L1-Blockchain and Rift-Network are historical prototypes and design inputs. Their behavior is not normative. A compatibility adapter may be built only after the formal model is stable and a conformance suite exists.
