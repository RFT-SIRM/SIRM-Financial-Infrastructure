# Constants Register

This register separates adopted SIRM policy inputs from superseded prototype values, unrelated research quantities, and parameters that have not been selected. A value appearing in a legacy repository is not normative merely because it has a name or a historical implementation.

## 1. Adopted initial policy inputs

### Founder genesis rate

- `founderRatePpm = 13_090`
- `ppmScale = 1_000_000`
- Exact percentage: `13,090 / 1,000,000 = 0.01309 = 1.309%`
- One-time allocation: `founderAllocation(G) = G × 13_090 / 1_000_000`, using integer division rounded down.
- Remainder: `remainingGenesisPool(G) = G − founderAllocation(G)`.

These are the current Lean definitions in `SIRM/FinancialCore.lean`. The model includes the founder-rate equality, the allocation upper bound, and the founder-plus-remainder identity. The rate is a genesis policy input, not future inflation, fee entitlement, or an economic-optimality theorem.

One basis point is 0.01%; therefore 1.309% is 130.9 basis points. PPM is used because it represents the selected rate exactly as an integer.

## 2. Superseded prototype value

- Former Rift founder share: `31_400 ppm = 3.14%`.
- Status: **superseded; not the current SIRM policy**.
- The adopted value is 13,090 ppm. No legacy constant silently overrides the Lean definition.

## 3. Historical fields not adopted by SIRM

The following values appeared in earlier prototype material and are retained here only as migration/review references:

- `NEG_E = -2,718,281,828,459,045,235` — not adopted pending a precise account-level interpretation and proof.
- `MIN_FIELD_PRESSURE = 1,000,000` — not adopted as a normative SIRM parameter.
- Legacy edge cost: `10^21` in one Solana prototype and `10^9` in an L1 simulator — conflicting historical scales; neither is adopted.

These values must not be imported into normative state transitions without a documented semantic definition, unit, authority, and proof of the intended account-level behavior. See [Migration from Rift](MIGRATION_FROM_RIFT.md).

## 4. Research quantity that is not a token parameter

Phi-Genesis has a distinct spectral quantity numerically near `1.30912892028081…`. It is not the 1.309% founder rate, not a ppm constant, and not a tokenomics parameter. Its research proof status belongs to the Phi-Genesis workstream.

## 5. Parameters not yet selected

The following remain explicit decisions rather than implicit defaults:

- total genesis supply and token decimals;
- founder address, account class, custody, and vesting;
- treasury, validator, ecosystem, community, and other initial allocations;
- network fee schedule, issuance, burn, staking, rewards, and any supply cap;
- asset registry, account registry, and account lifecycle policy;
- consensus, validator admission, and protocol-upgrade parameters.

No unselected value should be inferred from an example, a legacy prototype, or a research scalar.

## 6. Required record for future constants

Every adopted protocol parameter must record:

- exact name and semantic meaning;
- unit and valid range;
- integer representation and rounding rule;
- overflow/underflow behavior and residual destination;
- authority allowed to change it;
- approval threshold and timelock;
- effective protocol version or epoch;
- linked Lean definition, theorem obligations, tests, and decision record.

A parameter change must update the normative specification, Lean definitions and proofs, tests, this register, and the relevant architecture decision together.
