# Open Source, Transparency, and Public Verification

## Source license

New code and documentation in this repository are licensed under Apache License 2.0. This license applies only to material in this repository and does not relicense the historical Rift repositories, other RFT repositories, or third-party dependencies. Each dependency retains its own license.

## What is intended to be public

- protocol source and version history;
- mathematical definitions, theorems, assumptions, and formalization status;
- build configuration and reproducible CI evidence;
- transaction format and state-transition rules when implemented;
- validator and governance rules;
- independent audit reports, remediation status, and release artifacts;
- public state commitments and transaction-verification tools, subject to privacy protections.

## Transparency is not disclosure of personal data

Public verifiability must not require publishing names, identity documents, account credentials, or confidential customer/institutional data. The system needs an explicit privacy model, selective disclosure, and data-minimization rules before production. A public protocol and a private customer identity layer can coexist only if their interfaces and trust assumptions are specified.

## No impossible-security promise

Open source makes independent inspection possible; it does not make a system impossible to exploit. Security requires reviewed code, robust key custody, independent operators, consensus analysis, audits, incident response, and legally accountable institutions where real assets are involved. No one should be asked to trust the founder or a single operator simply because the project is open source.

## Public assurance record

Each release should publish the exact source commit, toolchain/dependency versions, formal build result, implementation test results, audit reports, known limitations, and any accepted risks. A failed or empty build must never be presented as a successful formal verification result.