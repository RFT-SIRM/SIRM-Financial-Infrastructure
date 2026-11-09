# Mathematical Scope and Assurance Boundaries

The current Lean core defines aggregate supply, issuance, burn, transfer, and exact 1.309% genesis allocation. The accounting module defines balanced signed journal entries and aims to prove aggregate signed-balance conservation.

These are foundation theorems, not a complete banking or blockchain proof.

Not yet proved: account ownership and authorization; solvency or reserve backing; redemption at par; Rust correspondence; consensus safety/finality; censorship resistance; custody key security; legal enforceability or regulatory compliance.

Critical next step: relate individual balances, effective participant balances, participant set, global field, journal and supply counters. An aggregate scalar must not be assumed equal to the sum of individual accounts unless that equality is defined and proved.

Formalization order: typed assets/accounts; balanced postings; transfers and debt limits; issuance/redemption; global-field refinement; pending pools and dust; governance; reserve attestations as external assumptions; reachable-state safety theorem.
