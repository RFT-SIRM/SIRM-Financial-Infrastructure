# Release Gates

## A — Formal accounting
Pinned reproducible build; actual SIRM target compiled; `lake test` has a real test driver and passes; issuance, burn, journal and account invariants; no sorry or unreviewed axioms in normative proofs. Runtime/property tests and linting remain separate follow-up requirements.

## B — Reference execution
Rust implementation, canonical serialization, checked arithmetic, atomic failure, differential/property/fuzz/replay tests, migration tests and independent audit.

## C — Native development network
Deterministic block execution, durable ledger, state root, peer authentication, validator lifecycle and written consensus fault model. No real customer value.

## D — Adversarial testnet
Independent audits; partition, equivocation, censorship, compromise, restart and recovery exercises; tested governance and upgrades.

## E — Institutional pilot
Legal entity and authorization, custody, reserve and redemption terms, independent reserve attestation, privacy/security/compliance review.

## F — Production
Independent formal, implementation, consensus, security and operational sign-offs; public genesis parameters; no unresolved critical/high findings.

Passing one gate does not imply later gates.
