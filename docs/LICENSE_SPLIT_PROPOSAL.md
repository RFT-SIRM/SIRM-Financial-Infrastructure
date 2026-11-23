# License split proposal — background; superseded by the owner's decision of 2026-11-23

> **Update:** the owner decided to put this whole repository under BUSL-1.1 instead of splitting it (see `docs/DECISIONS.md`, `LICENSE`). The text below is the earlier reasoning and is kept unchanged.

**Status:** proposal. `LICENSE` is unchanged. This repository remains Apache-2.0. No separate
repository exists yet. This document is not legal advice; read it with
[`LICENSING_AND_IP_POLICY.md`](LICENSING_AND_IP_POLICY.md) (especially sections 3, 6, 7 and 10).

## Why split instead of relicensing this repository

- Everything already published under Apache-2.0 stays Apache-2.0 for the people who hold copies.
  Replacing `LICENSE` now would protect only future versions (policy section 3).
- The value of this repository is that anyone can inspect and reproduce the specification, the
  Lean development, the test vectors and the reference code. Business Source License 1.1 is
  source-available, not open source; it would reduce independent review, which this project
  needs and does not yet have.
- What is expensive to copy is not the specification but a running network, its operators, its
  name and its regulatory standing. Those are protected by a separate license on the production
  implementation and by a naming policy, not by closing the specification.

## What stays Apache-2.0 (this repository)

The formal specification and Lean models; theorem-level tests; encoding, signature and
commitment specifications and their frozen vectors; Python reference implementations; the
`rust/sirm-codec` crate as a conformance reference; documentation. These are meant to be reused
by independent, conforming implementations.

## What would be licensed separately (not yet created)

A future production node and validator implementation, network operations tooling, and
institutional applications, each in its own repository (policy section 6). Rule: a separate
repository may depend on the Apache-2.0 material; Apache-2.0 material is never moved out of
Apache-2.0 retroactively.

## Proposed Business Source License 1.1 parameters (for the owner to decide)

| Parameter | Proposal |
|---|---|
| Licensor | the project owner (exact legal name to be filled in) |
| Licensed Work | the named production implementation, per released version |
| Additional Use Grant | any non-production use; **production use to operate a node or validator on the RFT Network or a test network is allowed**; offering the Licensed Work, or a service built on it, to third parties as a competing commercial product or independent value-bearing network requires a commercial license |
| Change Date | four years after the first public release of each version (the standard maximum) |
| Change License | Apache-2.0 |

Reasoning for the operator clause: policy section 7 requires that a production restriction must
not prevent independent operation of a network meant to be independently verifiable.
The standard BUSL-1.1 text is used unchanged; only the parameters above are filled in.

## Gates before the first BSL release

1. The owner confirms the parameters in writing in `docs/DECISIONS.md`.
2. A lawyer reviews the exact parameter text once (the standard license text is not rewritten).
3. Copyright holder identified; the repository has had no outside contributors so far, so the
   owner holds the copyright in its own contributions. Parts written with AI assistance have
   legally uncertain authorship; this is recorded, not resolved here.
4. Decide on contributor terms (CLA or none) **before** accepting any outside contribution to the
   BSL repository, because relicensing later needs every contributor's consent (policy section 4).
5. Every file carries an SPDX identifier (`Apache-2.0` or `BUSL-1.1`) so the split is visible.
6. The naming policy ([`TRADEMARK_AND_NAMING_POLICY.md`](TRADEMARK_AND_NAMING_POLICY.md)) is in place.

## What this does not do

It does not stop anyone from using, copying or forking what is already published under
Apache-2.0. It does not register any trademark. It does not give legal certainty; it is a
direction with explicit gates.
