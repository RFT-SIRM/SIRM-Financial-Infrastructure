# Constants Register

| Parameter | Value | Status |
|---|---:|---|
| Founder genesis share | 13,090 ppm = 1.309% | Adopted initial policy |
| Former Rift founder share | 31,400 ppm = 3.14% | Superseded |
| PPM scale | 1,000,000 | Definition |
| Phi-Genesis spectral value | approximately 1.30912892028081… | Research result; not the token rate |
| Legacy NEG_E | -2,718,281,828,459,045,235 | Not adopted pending account-level proof |
| Legacy MIN_FIELD_PRESSURE | 1,000,000 | Not adopted |
| Legacy edge cost | 10^21 in Solana prototype; 10^9 in L1 simulator | Conflicting; not adopted |
| Total genesis supply / decimals | Unselected | Requires explicit decision |

1.309% = 0.01309 = 13,090 / 1,000,000. One basis point is 0.01%, so 1.309% is 130.9 basis points and is not an integer number of basis points. PPM is used to represent it exactly. For supply G, founder = floor(G × 13,090 / 1,000,000). The rate is one-time at genesis, not future inflation or fees.

Every protocol parameter must specify units, range, rounding, overflow, authority, approval threshold, timelock and effective epoch.
