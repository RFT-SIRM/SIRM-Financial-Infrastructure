# SIRM Financial Infrastructure

[![RFT-SIRM Research Hub](https://img.shields.io/badge/RFT--SIRM-Research%20Hub-5b4bc4?style=flat-square)](https://github.com/RFT-SIRM/UltraCore-RFT)
[![Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-4777bd?style=flat-square)](LICENSE)
[![Lean CI](https://github.com/RFT-SIRM/SIRM-Financial-Infrastructure/actions/workflows/lean.yml/badge.svg?branch=main&style=flat-square)](https://github.com/RFT-SIRM/SIRM-Financial-Infrastructure/actions/workflows/lean.yml)
[![Lean 4 specification](https://img.shields.io/badge/Formal%20specification-Lean%204-168f83?style=flat-square)](docs/FORMALIZATION_STATUS.md)
[![Rust reference implementation](https://img.shields.io/badge/Rust%20reference-Planned-d97706?style=flat-square)](docs/ARCHITECTURE.md)

**The normative financial-state and accounting specification for SIRM Protocol, formalized in Lean 4.**

SIRM Financial Infrastructure defines financial state, admissible operations, accounting relationships, and safety invariants. The Lean development is the source of truth for the protocol's mathematical semantics. A deterministic Rust reference implementation and the independent RFT Network are planned downstream stages; neither is represented as complete.

## 1. Where this project fits

[UltraCore-RFT](https://github.com/RFT-SIRM/UltraCore-RFT) is the wider **RFT-SIRM research and engineering hub**. This repository is the dedicated financial-infrastructure workstream within that ecosystem: it owns the SIRM financial model, its Lean definitions, and the record of what has and has not been proved.

**RFT** means *Resonant Field Theory*. **SIRM** means *Synthetic Intelligence Reasoning Model*. Within this workstream, **SIRM Protocol** is the normative financial state-transition specification; **RFT Network** is the planned independent execution and settlement network; **RFT** is the planned native network asset.

The hub link is a project-navigation and research-lineage relationship. It does not imply a separate legal entity, corporate subsidiary, partnership, institutional endorsement, or deployed financial network. Older Rift repositories are historical prototype sources, not automatic authorities for the new protocol; see [Migration from Rift](docs/MIGRATION_FROM_RIFT.md).

## 2. A Note on Origin and Purpose

This project does not ask to be judged by the status, reputation, or promises of its author. It asks to be examined through its foundations: where its ideas come from, what principles guide its development, what has been formally established, and what remains to be proven.

SIRM Financial Infrastructure is one workstream within the RFT-SIRM research and engineering programme. Its purpose is to develop a rigorous financial foundation in which rules are explicit, accounting is coherent, authority is constrained, and critical state transitions can be examined mathematically.

The direction is deliberate: define before implementing; prove before claiming; preserve evidence and document assumptions; distinguish mathematical results from engineering, institutional, and legal claims; and make every major step open to independent examination.

The plan is public. The decisions are documented. The results are subject to verification.

The ambition is long-term, but progress must remain measurable. No destination is treated as achieved merely because it has been announced.

**Judge the work by its foundations, its evidence, and the path it is prepared to make visible.**

## 3. What We Are Building — Eight Layers

The cards below are a visual guide to the formal Lean foundation. Each illustration is an independent, repository-local SVG asset, so it can be rendered and reviewed separately.

<table>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/financial-state.svg" width="88" height="88" alt="Ledger and accounting scales"/></p>
<strong>1. Financial State &amp; Accounting</strong><br/>
Balances, supply reconciliation, balanced journals and aggregate ledger conservation.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/authority-control.svg" width="88" height="88" alt="Shield and key"/></p>
<strong>2. Authority &amp; Account Control</strong><br/>
Operation grants and principal/account control are separate requirements.
</td>
</tr>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/registries-assets.svg" width="88" height="88" alt="Typed registries database"/></p>
<strong>3. Typed Registries &amp; Assets</strong><br/>
Finite account and asset registries carry lifecycle, issuer, precision and network metadata.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/precise-units.svg" width="88" height="88" alt="Exact arithmetic calculator"/></p>
<strong>4. Exact Asset Units</strong><br/>
Integer base-unit conversion avoids floating point and silent nonzero rounding.
</td>
</tr>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/cross-network-math.svg" width="88" height="88" alt="Connected network units"/></p>
<strong>5. Cross-Network Mathematics</strong><br/>
Exact rational conversion carries residuals in rate- and partition-scoped accumulators.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/atomic-migration.svg" width="88" height="88" alt="Paired migration arrows"/></p>
<strong>6. Authorized Atomic Migration</strong><br/>
One abstract transition pairs source burn, destination issuance, both journals and residual update.
</td>
</tr>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/replay-protection.svg" width="88" height="88" alt="Replay protection shield"/></p>
<strong>7. Global Financial Replay Protection</strong><br/>
Transfer, issuance and burn share one expected nonce per principal; typed request IDs bind exact retries to cached responses.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/formal-verification.svg" width="88" height="88" alt="Formal proof and independent audit checklist"/></p>
<strong>8. Formal Verification &amp; PR Assurance</strong><br/>
Lean builds the specification and theorem regressions; the pull-request gate runs 17 independent static audits.
</td>
</tr>
</table>

**Current boundary:** these cards describe the formal Lean model and its theorem regressions, not a deployed production service. The Rust reference implementation, production transaction processor, independent RFT Network, custody, reserves and institutional services remain future work with separate evidence gates.

## 4. Mission and development principle

Financial infrastructure needs explicit state and accounting rules, not only application code or operational promises. The project follows this order:

1. define the financial state and admissible transitions;
2. state the accounting and safety invariants;
3. prove transition preservation and reachable-state properties in Lean 4;
4. compile concrete theorem-level regression scenarios;
5. develop a separate deterministic Rust reference implementation;
6. establish and document its refinement/conformance relationship to Lean;
7. address network, security, institutional, and legal requirements through separate release gates.

A theorem applies only to its formal statement and assumptions. A green Lean build does not by itself certify a Rust executable, network, custodian, reserve, legal entity, or production financial service.

## 5. What the Lean model currently covers

The source is organized by responsibility rather than a wide module table.

### Financial state and supply

- `SIRM.FinancialCore` defines the supply state, initial state, issuance and burn transitions, and the one-time founder-allocation arithmetic.
- `SIRM.Holdings` defines nonnegative holder balances indexed by account and asset, with per-asset reconciliation to outstanding supply, funded transfers, issuance, and holder-bounded burns.

### General ledger and holder reconciliation

- `SIRM.Accounting` defines signed per-asset journal entries and conservation for balanced postings.
- `SIRM.HolderAccountingBridge` supplies matching journals for holder transfers, issuance, and burns, with pointwise subledger-agreement preservation under an unmapped-counterpart-account assumption.
- Holder balances and the signed general ledger are distinct projections. They are related by explicit posting rules; they must not be added together as if they measured the same quantity.

### Authorization and reachable-state safety

- `SIRM.Authorization` provides abstract, state-dependent authorization predicates and guarded transfer, issue, and burn operations. Issuance authorization explicitly distinguishes the issuer account from the recipient.
- `SIRM.AuthorityRegistry` stores finite static grants binding a principal, exact operation scope, asset, and maximum amount. An issue grant binds both issuer and recipient.
- `SIRM.AccountControl` defines a separate finite principal/account control relation. The combined policy requires control of the transfer source, issue issuer, or burn holder, as well as the exact operation grant. The recipient need not be controlled by the issuing principal when the grant explicitly authorizes that recipient.
- `SIRM.TypedRegistry` defines distinct finite account and asset identifier types, total metadata registries, account classes and lifecycle statuses, and asset decimal precision, issuer, status, and network metadata. The asset registry carries a proof that each issuer is on the asset's declared network.
- `SIRM.AssetUnits` converts explicit nonnegative decimal coefficients into integer asset base units without floating point or rounding. Excess decimal precision is accepted only when the excess digits are zero; a separate `Fin`-bounded adapter enforces a caller-supplied maximum without selecting a production machine width.
- `SIRM.AssetMigration` models explicit cross-network routes and positive rational base-unit rates. Quotient/remainder conversion is exact; residual dust is carried in a rate- and partition-indexed accumulator, never silently discarded or pooled across partitions. This is arithmetic and route eligibility, not a complete bridge transaction.
- `SIRM.AuthorizedAssetMigration` defines one proof-carrying transition that atomically burns source units, issues the target amount released by route-specific dust, posts both balanced holder/GL journals, and preserves the combined financial invariant. The dust claim subledger is scoped to one route, source holder, and recipient.
- `SIRM.ReplayProtectedAssetMigration` wraps that transition in a per-principal sequential nonce gate: only the exact next nonce is accepted, and the nonce advances in the same abstract state as the migration.
- `SIRM.ReplayProtectedFinancialMachine` extends the same sequential nonce policy across transfer, issue, and burn in one abstract financial state update.
- `SIRM.FinancialTransactionEnvelope` binds a typed operation payload and request ID to a stored response: exact retries are state no-ops, request-ID conflicts and nonce mismatches cannot be admitted as successful new requests, and the reachable-state invariant includes receipt consistency.
- `SIRM.RegistryAwareFinancialMachine` composes the existing authority-grant and account-control policy with typed-asset issuance eligibility. Issuance requires an active asset and active issuer; transfer and burn authorization predicates remain unchanged. The adapter reuses the combined financial conservation theorem.
- `SIRM.StateMachine` proves a generic reachable-state invariant from initial-state and transition-preservation obligations.
- `SIRM.AuthorizedStateMachine` applies this pattern to authorization-gated holder transitions.

### Integrated financial transition

- `SIRM.AuthorizedFinancialMachine` combines holder balances and the signed general ledger in one abstract financial state. Its authorized transfer, issuance, and burn steps update both projections together.
- `SIRM.EscrowAccounting` adds a separately authorized, single-use escrow lifecycle: deposit to a dedicated vault holder, release to the recorded beneficiary, or cancellation back to the depositor. Exact vault backing, supply reconciliation, mapped subledger agreement and aggregate GL conservation are preserved.
- Its machine invariant preserves holder/supply reconciliation, mapped subledger agreement, and aggregate signed-ledger balance relative to the opening ledger.
- `SIRMTests.lean` contains concrete theorem-level regression scenarios, including an integrated transfer → issuance → burn trace.

For theorem-by-theorem status, explicit assumptions, and remaining obligations, see [Formalization Status](docs/FORMALIZATION_STATUS.md) and [Mathematical Scope](docs/MATHEMATICAL_SCOPE.md).

## 6. Genesis allocation policy

> **SELECTED ONE-TIME GENESIS INPUT**
>
> **Founder rate: 1.309% · 13,090 ppm**
>
> Let `G` be the total genesis supply in the smallest integer accounting unit.
>
> **Founder allocation:** `A(G) = floor((13,090 × G) / 1,000,000)`
>
> **Remainder:** `U(G) = G − A(G)`
>
> The division is rounded down to a whole base unit, matching natural-number division in Lean. The remainder stays explicitly unallocated; it is not silently assigned to the treasury or another pool.

The Lean model states the exact rate and proves:

- `founderAllocation(G) ≤ G`;
- `founderAllocation(G) + remainingGenesisPool(G) = G`.

For example, if `G = 1,000,000,000,000` base units, the founder allocation is `13,090,000,000` base units. This is an arithmetic example, not a decision about total supply or token decimals.

The 1.309% rate is an adopted one-time policy input, not a theorem of economic optimality. It grants no automatic right to future issuance, fees, treasury assets, reserves, validator rewards, governance control, or protocol administration. Other genesis pools, the total supply, decimals, receiving address, custody, and vesting remain separate decisions. See [Tokenomics](docs/TOKENOMICS.md) and the [Constants Register](docs/CONSTANTS_REGISTER.md).

## 7. Why Lean 4

Lean 4 provides a formal language and a small trusted kernel for checking proof terms. Here it is used to express financial state, guarded transitions, arithmetic preconditions, journal balance, reconciliation, authorization predicates, and invariants over reachable states.

Formal proof does not remove the need to review the model. A proof may be correct while the modeled account universe is incomplete, an assumption is too strong, or correspondence to a future implementation has not yet been established. The project therefore keeps present declarations, assumptions, and open obligations visible.

## 8. Target architecture: Lean → Rust → RFT Network

<table>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/formal-verification.svg" width="88" height="88" alt="Lean 4 normative specification and proof checks"/></p>
<strong>1. SIRM Protocol — Lean 4</strong><br/>
<sub><strong>Current · normative specification</strong></sub><br/>
Formal financial-state and transition model, checked through Lean builds and theorem-level regressions.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/rust-reference.svg" width="88" height="88" alt="Planned deterministic Rust reference implementation"/></p>
<strong>2. Rust Reference Implementation</strong><br/>
<sub><strong>Planned · deterministic execution</strong></sub><br/>
A separate implementation of the specified transitions, with its own refinement and conformance evidence.
</td>
</tr>
<tr>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/rft-network.svg" width="88" height="88" alt="Future independent RFT network"/></p>
<strong>3. Independent RFT Network</strong><br/>
<sub><strong>Future · network and settlement</strong></sub><br/>
Independent nodes, consensus, data availability and settlement require separate specifications and evidence.
</td>
<td width="50%" valign="top">
<p align="center"><img src="docs/assets/overview/institutional-applications.svg" width="88" height="88" alt="Future institutional applications and integrations"/></p>
<strong>4. Institutional Applications</strong><br/>
<sub><strong>Future · external integrations</strong></sub><br/>
Adapters and institutional services require independent security, custody, reserve, legal and operational gates.
</td>
</tr>
</table>

The Rust implementation is intended to be a separate implementation of the specified transition semantics. It is **not** produced by translating Lean source, and passing tests alone will not make it authoritative. Its workstream must include canonical serialization, checked arithmetic, deterministic failure behavior, differential/property tests, and a documented refinement/conformance argument.

The RFT Network is a later, independent stage. No consensus algorithm is selected in this foundation. Node identity, validator lifecycle, consensus safety and liveness, data availability, recovery, and network security require their own specifications and evidence. Institutional applications remain a further layer; they cannot turn external custody, reserves, or legal claims into Lean-proved facts.

## 9. Verification and current test scope

The repository's pinned workflow exposes 18 independent job checks on each pull request: one Lean job runs the normative build and theorem-level test driver, while 17 lightweight static audits independently check authorization boundaries, account control, integration, toolchain pins, and documentation. The Lean build is not repeated by the static jobs. The theorem suite also covers single-use escrow deposit/release/cancel transitions; concurrent escrow IDs, dispute handling and external settlement finality remain open.


```bash
lake build
lake test
```

See [Lean CI](.github/workflows/lean.yml) and [Testing and Verification](docs/TESTING.md). The test driver compiles concrete theorem scenarios in `SIRMTests.lean`; it is not a randomized node test, runtime fuzzing campaign, or network test. Linting remains disabled until a dedicated lint driver is configured.

A passing build is evidence about the exact source revision and pinned toolchain. It is not evidence that the future Rust implementation, consensus protocol, production system, or institutional operations have passed their separate gates.

## 10. What remains outside the current proofs

The current declarations do **not** yet establish:

- a complete canonical asset registry or a production account universe;
- legal ownership of accounts or a concrete principal-to-account mapping;
- cryptographic signatures, key custody, signer thresholds, or production permission administration;
- a complete genesis assignment to founder, treasury, validators, ecosystem, community, and other real accounts;
- the production execution envelope: canonical bytes and hashing, signer/threshold rules, expiry, fees, events, deterministic error schemas, persisted idempotent responses, rollback/recovery, and a concrete runtime refinement. The Lean model now has an abstract global financial nonce and typed request-ID receipt semantics, but does not yet formalize authorization-rejection caching or prove a database/runtime implementation;
- production runtime atomicity or Rust/Lean refinement;
- reserve backing, solvency, redemption, or external asset existence;
- governance, validator-set changes, consensus safety/finality, censorship resistance, or data availability;
- privacy guarantees, legal enforceability, or regulatory compliance.

The combined Lean financial machine does model holder and journal updates in one abstract transition. That is a mathematical state-transition result, not a claim that a production transaction processor, serialization format, signature system, or runtime has been implemented.

The staged requirements are recorded in [Release Gates](docs/RELEASE_GATES.md). Passing one gate does not imply that a later gate has passed.

## 11. Documentation map

### Protocol and financial model

- [Protocol Specification](docs/PROTOCOL_SPEC.md) — normative transition and determinism requirements.
- [Architecture](docs/ARCHITECTURE.md) — Lean, Rust, network, and application boundaries.
- [Accounting Model](docs/ACCOUNTING_MODEL.md) — holder balances and signed-ledger projections.
- `SIRM.FeeAccounting` — exact gross/net/fee decomposition, separately authorized fee transfers, balanced three-role holder/GL posting, and preservation of holder/supply and aggregate-ledger invariants. The fee collector is explicitly a holder in this initial model; tariff policy and non-holder revenue-account classification remain open.
- [Tokenomics](docs/TOKENOMICS.md) — founder genesis policy and unresolved supply decisions.
- [Constants Register](docs/CONSTANTS_REGISTER.md) — adopted, superseded, and unselected parameters.
- [RFT Network](docs/RFT_NETWORK.md) — intended independent network scope.

### Formal evidence and delivery status

- [Formalization Status](docs/FORMALIZATION_STATUS.md) — present Lean declarations and open proof obligations.
- [Mathematical Scope](docs/MATHEMATICAL_SCOPE.md) — precise theorem scope, assumptions, and limits.
- [Testing](docs/TESTING.md) — pinned build and theorem-level regression scope, including exact fee arithmetic.
- [Release Gates](docs/RELEASE_GATES.md) — staged proof, implementation, network, and production gates.
- [Roadmap](docs/ROADMAP.md) — development phases and incomplete work.
- [Session Workflow](docs/SESSION_WORKFLOW.md) — mandatory handoff, Lean debugging, and verification protocol for future sessions.

### Governance, security, and operation

- [Governance](docs/GOVERNANCE.md) — decision authority and change control.
- [Security Model](docs/SECURITY_MODEL.md) — authorization, threats, and security assumptions.
- [Consensus Requirements](docs/CONSENSUS_REQUIREMENTS.md) — requirements before a consensus design is selected.
- [Network Protocol](docs/NETWORK_PROTOCOL.md) — future transport and network protocol boundaries.
- [Institutional Layer](docs/INSTITUTIONAL_LAYER.md) — future external services and institutional interfaces.

### Decisions, migration, and stewardship

- [Architecture Decisions](docs/DECISIONS.md) — adopted and unresolved design decisions.
- [Migration from Rift](docs/MIGRATION_FROM_RIFT.md) — treatment of legacy prototype material.
- [Open Source and Transparency](docs/OPEN_SOURCE_AND_TRANSPARENCY.md) — public development and evidence practices.
- [Licensing and IP Policy](docs/LICENSING_AND_IP_POLICY.md) — repository license and intellectual-property boundaries.
- [Contributing](CONTRIBUTING.md) — contribution and review requirements.
- [Security Policy](SECURITY.md) — responsible vulnerability reporting.

## 12. License, identity, and responsible use

The repository's formal specification, Lean source, theorem-level tests, and covered documentation are distributed under the **Apache License 2.0**, subject to any file-specific or third-party notices. The root [LICENSE](LICENSE) is authoritative. See [Licensing and IP Policy](docs/LICENSING_AND_IP_POLICY.md) for contribution rights, project identifiers, and the treatment of possible future commercial components.

This repository is not a bank, payment service, custodian, exchange, deposit-taking institution, live settlement network, reserve attestation, or regulatory authorization. Nothing here promises redemption, solvency, deposit insurance, or legal enforceability. A production deployment would require independent implementation, security, operational, custody, reserve, privacy, legal, and jurisdiction-specific regulatory evidence.

---

**Project home:** [RFT-SIRM Research and Engineering Hub — UltraCore-RFT](https://github.com/RFT-SIRM/UltraCore-RFT) · **Financial specification:** [SIRM Financial Infrastructure](https://github.com/RFT-SIRM/SIRM-Financial-Infrastructure)
