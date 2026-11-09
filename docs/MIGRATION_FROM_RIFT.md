# Migration from Rift-L1-Blockchain and Rift-Network

## Naming
The target is SIRM Financial Infrastructure / SIRM Protocol / RFT Network / RFT asset. Rift is retired as the target system name.

## Retain as design input
Global-field distribution, participant accounts, effective-balance concept, aggregate supply counters, edge-cost idea, pause controls, pending distribution, deterministic planner and separation of core from network interfaces.

## Do not copy as normative behavior
The prototypes contain unresolved accounting semantics and are not line-by-line migration sources.

### Aggregate base sum
The Solana prototype registers a participant with base balance zero while subtracting the global field from an aggregate base sum. That aggregate cannot simply be assumed to equal the sum of stored participant base balances. Define its semantics and prove reconciliation.

### Effective balance
A candidate convention is effectiveBalance = baseBalance + globalField. Registering at zero effective balance would require baseBalance = -globalField. This is a candidate model, not adopted until all transitions are proved.

### Exit and burn
Exit must derive the removed claim from effective balance and reconcile it with journal and supply postings. Raw base balance must not be confused with effective balance.

### Dust
Modulo normalization can discard complete multiples when participant count changes. Pending value must be preserved in an explicit pool and allocated later; it must never disappear.

### Negative entropy / field decay
Changing a global field and compensating an aggregate scalar does not by itself establish account-level conservation. Choose and prove whether the operation is a burn, transfer or another transition. Legacy NEG_E is not adopted.

### Issuance
Legacy field-pressure minting is not carried forward until its unit, authority, economic purpose and liability/reserve relationship are specified.

No historical balances are migrated without a versioned conversion, conservation proof, reconciliation and independent tests.
