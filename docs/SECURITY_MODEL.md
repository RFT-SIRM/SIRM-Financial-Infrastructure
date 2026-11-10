# Security Model and Assurance Boundaries

## Threats to address

- unauthorized issuance, burning, transfers, upgrades, or changes to fee parameters;
- compromised signing keys, malicious insiders, collusion, and governance capture;
- arithmetic overflow/underflow, rounding exploitation, replay, duplicate execution, and transaction-ordering abuse;
- account, asset, mint, program, or state-root substitution;
- consensus equivocation, censorship, network partitions, and invalid finality claims;
- unavailable or corrupted state data, unsafe snapshots, and failed migrations;
- reserve misrepresentation, custody failure, oracle errors, and insolvency;
- privacy leaks, metadata correlation, and disclosure of customer information;
- supply-chain compromise, malicious dependencies, and unsafe release processes.

## Required controls

- least-privilege and separated roles for validators, treasury, governance, and operational maintainers;
- threshold authorization for high-impact actions, timelocks, public notices, key rotation, and emergency pause/recovery procedures;
- canonical asset identifiers and canonical mint/contract binding;
- checked arithmetic, exact integer units, explicit rounding, and atomic state transitions;
- deterministic replay and conformance tests against the Lean specification;
- independent code review, external security audits, reproducible builds, and signed releases;
- state commitments, independently verifiable transaction inclusion, and archival/data-availability procedures;
- explicit privacy policy and data minimization;
- independent reserve evidence and reconciliation where a product makes reserve or redemption claims.

## Formalized authorization boundary

The Lean model now separates two policy inputs. The authority registry grants an exact operation, asset, and amount limit; the account-control registry records a static principal/account relation. The combined policy requires both conditions for the relevant account: transfer source, issue issuer, or burn holder. An issue grant binds both issuer and recipient, while the recipient does not need to appear in the issuer's control relation.

These are mathematical policy inputs, not identity proofs. The static relation does not establish legal title, beneficial ownership, private-key possession, signature validity, enrollment, revocation, or production permission administration. The modeled issuance credits the recipient and increases supply; it does not debit the issuer. The separate general-ledger counterpart posting remains an accounting operation, not evidence that the issuer funded the issuance.

## What public verification does not guarantee

Open source and a public ledger improve inspectability; they do not make theft or compromise impossible. A formal proof does not establish that private keys remain secret, validators are honest, a software build matches reviewed source, a reserve exists, an off-chain custodian is solvent, or a legal promise is enforceable. Those require operational controls, independent evidence, audits, and enforceable institutional arrangements.

## Key rule

No founder, operator, or single gate key should have an unrestricted unilateral ability to rewrite finalized history, mint without policy limits, confiscate balances, or silently change the protocol. Emergency powers must be narrow, disclosed, time-limited, auditable, and subject to independent governance review.