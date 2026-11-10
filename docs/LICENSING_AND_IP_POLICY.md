# Licensing and Intellectual Property Policy

**Status:** Project policy for the SIRM Financial Infrastructure repository
**Repository license:** Apache License 2.0 (`Apache-2.0`)
**Scope:** Formal specification, Lean source, theorem-level tests, and
repository documentation, except where a file or third-party component
carries a separate license notice.

This document explains the project's licensing boundaries. It is not a
substitute for the applicable license text, a signed agreement, or legal
advice.

## 1. Why the formal foundation is open

SIRM Financial Infrastructure is the formal specification and assurance
foundation for the planned RFT financial infrastructure.

The project is developed around a deliberate separation:

1. specify financial state and transition rules mathematically;
2. prove stated safety properties in Lean 4;
3. test the formal development through the pinned build;
4. develop deterministic implementations and establish their
   correspondence with the specification;
5. subject network and institutional deployments to separate security,
   legal, operational, and regulatory review.

The formal foundation is intended to be independently inspectable,
reproducible, auditable, and usable as the basis for conforming
implementations.

Openness of the specification is intentional. It is not a claim that the
future network, software, financial services, or institutional operations
are already production-ready.

## 2. License governing this repository

The repository's governing license is the **Apache License, Version 2.0**.
The authoritative license text is the root [`LICENSE`](../LICENSE) file.

Subject to the conditions of Apache-2.0, recipients may use, reproduce,
modify, create derivative works of, and distribute covered material,
including for commercial purposes.

Important requirements and boundaries include:

- recipients must provide a copy of the license when distributing copies;
- required copyright, patent, attribution, and modification notices must
  be retained;
- the patent license is limited to the scope stated in Section 3 of
  Apache-2.0 and is subject to its termination provision;
- Apache-2.0 does not grant a general trademark license;
- the work is provided subject to the warranty disclaimer and limitation
  of liability in the license.

The full license terms control if this summary differs from the license.

Third-party components and files bearing their own license notices remain
subject to those notices. The presence of a dependency in the build does
not change that dependency's license.

## 3. Existing grants and version history

This policy does not purport to withdraw, cancel, or retroactively narrow
rights already granted for material distributed under Apache-2.0.

Replacing a repository's `LICENSE` file in a future commit would not, by
itself, revoke license grants already made for earlier copies or versions.

Any future licensing change must identify:

- the exact work and files affected;
- the version or release from which the change applies;
- the relevant copyright holders and their authority to grant the license;
- third-party material and existing license obligations;
- the treatment of previously distributed versions and contributions.

Previously granted Apache-2.0 rights must be respected.

## 4. Copyright, authorship, and contributions

A license grant is not the same as a transfer of copyright ownership.

The copyright in an individual contribution generally remains with its
copyright holder unless a separate valid agreement provides otherwise.
Submitting a contribution under Apache-2.0 does not by itself assign
ownership of that contribution to the repository maintainer.

Under Section 5 of Apache-2.0, a contribution intentionally submitted for
inclusion is licensed under Apache-2.0 unless the contributor explicitly
states otherwise or a separate agreement applies.

The contribution requirements are described in
[`CONTRIBUTING.md`](../CONTRIBUTING.md).

Contributors must have the right to submit their material and must identify
relevant third-party code, text, data, and other assets. Do not submit
material copied from another project unless its license permits the
intended use and all required notices are preserved.

This repository does not currently establish a general copyright
assignment or a separate dual-licensing agreement. No contributor should
assume that submitting a pull request transfers copyright ownership.

Before introducing a CLA, assignment, dual-licensing arrangement, or a
new contribution policy, the project must document the proposed terms and
obtain appropriate legal review.

## 5. Project names, marks, and affiliation

Project identifiers used in this ecosystem include:

- SIRM;
- SIRM Protocol;
- RFT;
- RFT Network;
- RFT-SIRM;
- project logos and related visual identity.

This list identifies names used by the project. It does not assert that
every name is registered as a trademark, establish ownership, or state
that any trademark application has been filed.

Apache-2.0 does not grant general rights to use a licensor's trade names,
trademarks, service marks, or product names. Its Section 6 permits the
customary descriptive use needed to identify the origin of the work.

A user, fork, implementation, publication, or service must not imply that
it is an official SIRM or RFT release, is sponsored by the project, or has
been reviewed, certified, endorsed, or approved by the project unless
there is a separate factual basis and appropriate permission.

This policy does not attempt to prohibit truthful descriptive references
that are permitted by applicable law and the governing license.

Ownership, registration, permissible use, and enforcement of project
marks require a separate review of the relevant names, logos, jurisdictions,
and rights holders.

## 6. Formal specification and future commercial products

This repository publishes the formal financial specification and its
proof-oriented development under Apache-2.0.

Future software and services may be developed and distributed as separate
components, for example:

- production node and validator software;
- network operations and hosted services;
- institutional treasury and settlement applications;
- custody integrations and operational tooling;
- enterprise support, deployment, and managed services.

A separate license may be selected for a genuinely separate component
where the relevant rights holders have authority to grant it.

A separate product license does not cancel Apache-2.0 rights in SIRM
material already distributed under Apache-2.0. If a future product includes
or derives from Apache-licensed material, the applicable Apache-2.0
permissions, notices, and obligations for that material must be respected.

The project must not describe an entire combined product as exclusively
proprietary if recipients continue to hold Apache-2.0 rights in components
included in that product.

## 7. Business Source License as a possible future option

The **Business Source License 1.1** (`BUSL-1.1`) is a possible candidate
for certain future, separately licensed implementation components. It is
not the license of this repository and is not adopted by this policy.

BUSL-1.1 is source-available, not an Open Source license. Its standard
terms grant rights to copy, modify, create derivative works, redistribute,
and make non-production use. A licensor may define an Additional Use Grant
that permits specified production use.

Each licensed version has parameters including the Licensor, Licensed Work,
Additional Use Grant, Change Date, and Change License. Under the standard
terms, the Change Date cannot be later than the fourth anniversary of the
first public distribution of the relevant version. The Change License must
be GPL-2.0-or-later or a license compatible with GPL-2.0-or-later.

Before BUSL-1.1 is used, the project must decide and publish those
parameters for the exact component. It must also consider the intended
rights of independent RFT Network operators, validators, institutions,
integrators, and users.

In particular, a production restriction must not accidentally prevent
independent operation of a network that is intended to be sovereign and
independently verifiable.

A commercial license may be offered separately for uses outside a future
component's published grant, but the commercial terms must be explicit.

The standard BUSL-1.1 text must not be casually rewritten. Any adoption
must be checked against the license's own terms and covenants.

## 8. Copyright, patents, and technical disclosures

Copyright generally protects original expression, such as source code,
documentation, diagrams, and other authored material. It does not, by
itself, create an exclusive right over mathematical facts, ideas,
procedures, systems, methods of operation, or algorithms.

Patent rights are separate from copyright and require a separate
patentability, inventorship, ownership, and jurisdictional analysis.

Public disclosure can affect patent options. Before publishing a technical
invention that may be considered for patent protection, the project should
obtain specialist advice on filing strategy and disclosure timing.

Nothing in this policy claims that a particular SIRM or RFT concept is
patentable, patented, novel, or exclusively controlled by the project.

## 9. Financial, banking, and regulatory boundary

This repository is a formal specification project. It is not itself:

- a bank or deposit-taking institution;
- a licensed money transmitter or payment service;
- a custodian, broker, exchange, or regulated financial intermediary;
- a deployed production blockchain or live settlement network;
- evidence of reserves, redemption rights, solvency, or deposit insurance;
- regulatory approval or legal authorization to provide financial services.

A Lean proof establishes only the proposition stated in the theorem,
under its explicit assumptions and the behavior of the trusted proof
environment. A successful build does not prove that a future software
implementation, validator network, custodian, reserve, or institution
conforms to the model.

The formalization status and release gates describe what has and has not
been established.

## 10. Review and change control

This policy must be reviewed before:

- changing the repository-wide license;
- introducing a separate license for a future implementation;
- accepting a contribution under terms other than Apache-2.0;
- adopting a CLA, copyright assignment, or dual-licensing arrangement;
- asserting ownership or registration of project marks;
- publishing patent-sensitive material;
- making commercial, institutional, banking, or regulatory claims.

A material licensing change requires a documented decision, identification
of the relevant rights holders, a review of third-party obligations, and
appropriate legal advice.

## 11. Authoritative references

- [Apache License 2.0 — full text](https://www.apache.org/licenses/LICENSE-2.0)
- [Apache License 2.0 — applying the license](https://www.apache.org/legal/apply-license)
- [Business Source License 1.1 — standard text](https://mariadb.com/bsl11/)
- [SPDX — BUSL-1.1 identifier and license metadata](https://spdx.org/licenses/BUSL-1.1.html)
- [U.S. Copyright Office — what copyright protects](https://www.copyright.gov/help/faq/faq-protect.html)

This policy is explanatory. The actual license texts and applicable law
control.
