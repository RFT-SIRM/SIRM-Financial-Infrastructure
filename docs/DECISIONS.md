# Architecture Decision Record

## Adopted in this foundational branch

1. **Project identity:** SIRM Financial Infrastructure is the project; SIRM Protocol is the normative financial protocol; RFT Network is the planned independent network; RFT is the planned native asset.
2. **Normative language:** Lean 4 is used for mathematical definitions and proofs. Rust is the planned execution implementation, not the source of protocol truth.
3. **Founder allocation:** one-time 1.309% genesis allocation, represented as 13,090 ppm and rounded down in the smallest base unit. It replaces the legacy 3.14% prototype field.
4. **Other genesis pools:** explicitly unallocated until separately decided. No total supply, token decimals, vesting, founder address, or reserve policy is inferred.
5. **Financial semantics:** signed double-entry conservation is distinct from natural-number supply accounting. They must not be conflated.
6. **Legacy field model:** not normative until its aggregate variables are given an account-level meaning and the optimized state is proved to refine direct account transitions.
7. **Network direction:** target an independent RFT network. Solana remains a historical prototype host and is not silently embedded as a permanent dependency.
8. **Public source license:** Apache License 2.0 is selected for this new repository. It does not automatically relicense the two older Rift repositories or third-party dependencies.

9. **Typed identifiers and registries:** account and asset identifiers use separate finite index types. Each finite registry is total over its declared identifier universe. Account class/status metadata is descriptive and does not itself grant authority. An asset's issuer must be in the account universe and on the asset's declared network. Asset migration arithmetic and transition semantics are specified separately in decisions 12–13.
10. **Issuance registry gate:** an authorized issuance must also target an active asset whose issuer account is active. The existing principal control and exact authority grant remain required. This registry gate does not alter transfer or burn authorization in the current formalization.
11. **Exact base-unit conversion:** decimal inputs are nonnegative integer coefficients with explicit decimal-place counts. Conversion to an asset's base units must be exact; nonrepresentable excess precision is rejected, never rounded implicitly. A range bound is supplied explicitly by the caller. No production decimals or machine integer width are selected here.
12. **Exact migration arithmetic:** a route supplies a positive rational rate in target base units per source base unit. Conversion records an exact quotient and residual numerator; residuals are carried forward, not rounded away. Dust accumulators are scoped to one exact rate and one explicit accounting partition. Both endpoint assets and issuers must be active for route eligibility, and the source and destination networks must differ. No production rate, pooling policy, or complete bridge execution semantics are selected.
13. **Atomic authorized migration step:** a formal migration transition must burn the selected source holder's units and issue only the target base units released by the route's exact residual accumulator in the same state transition. One principal must satisfy source burn control/grant and destination issuer control/issue grant; both route endpoints and both holder accounts must be active and on their respective networks. The exact residual claim is isolated by route, source holder, and recipient. This abstract step does not select replay protection, bridge finality, external custody, production liability posting for fractional dust, or valuation/backing policy.

14. **Migration replay guard:** the abstract replay-protected migration machine maintains an independent next nonce per principal, starts each sequence at zero, accepts only the exact expected nonce, and increments it atomically with the paired financial migration state. This is deliberately scoped to this migration machine; a global transaction envelope, request-hash/idempotent response cache, signatures, expiry, persistent nonce storage, concurrency control, and production integer-width behavior remain unselected.

## Not yet decided

- total genesis supply, decimals, and final allocation table;
- founder wallet, custody, vesting, and lock policy;
- consensus algorithm and validator participation model;
- network fee schedule, inflation, burn, staking, and reward policy;
- legal entity, regulated partners, product jurisdictions, and customer eligibility;
- privacy model and selective-disclosure mechanism;
- exact Rust implementation strategy and proof/refinement approach.

## Change control

Any change to an adopted decision must update this record, the relevant Lean definitions, the specification, and tests together. No code-level constant may silently override the normative record.
