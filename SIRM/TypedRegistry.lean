import SIRM.HolderAccountingBridge

/-!
# Typed Account and Asset Registries

AccountId and AssetId are distinct finite index types. Registry metadata
is total over each finite identifier domain.

Account classes are descriptive classifications, not authorization grants.
Asset/issuer activity is an additional eligibility condition; authority
grants and account-control proofs remain separate.
-/

namespace SIRM

/-- Network identifiers are distinct from account and asset identifiers. -/
structure NetworkId where
  value : Nat
  deriving DecidableEq, Repr

/-- Finite account identifier with a type-level universe size. -/
structure AccountId (accountCount : Nat) where
  index : Fin accountCount
  deriving DecidableEq, Repr

namespace AccountId

def equivFin (n : Nat) : AccountId n ≃ Fin n where
  toFun := fun account => account.index
  invFun := fun index => ⟨index⟩
  left_inv := by
    intro account
    cases account
    rfl
  right_inv := by
    intro index
    rfl

end AccountId

instance instFintypeAccountId (n : Nat) : Fintype (AccountId n) :=
  Fintype.ofEquiv (Fin n) (AccountId.equivFin n).symm

/-- Finite asset identifier; not interchangeable with AccountId. -/
structure AssetId (assetCount : Nat) where
  index : Fin assetCount
  deriving DecidableEq, Repr

namespace AssetId

def equivFin (n : Nat) : AssetId n ≃ Fin n where
  toFun := fun asset => asset.index
  invFun := fun index => ⟨index⟩
  left_inv := by
    intro asset
    cases asset
    rfl
  right_inv := by
    intro index
    rfl

end AssetId

instance instFintypeAssetId (n : Nat) : Fintype (AssetId n) :=
  Fintype.ofEquiv (Fin n) (AssetId.equivFin n).symm

/-- Account classification is descriptive, not an authorization grant. -/
inductive AccountClass where
  | holder
  | treasury
  | validatorPool
  | ecosystemPool
  | communityPool
  | unallocatedPool
  | control
  | custody
  | reserve
  | customerLiability
  | equity
  | income
  | expense
  | fee
  | escrow
  | clearing
  deriving DecidableEq, Repr

/-- Operational account lifecycle. -/
inductive AccountStatus where
  | active
  | frozen
  | closed
  deriving DecidableEq, Repr

/-- Asset lifecycle. -/
inductive AssetStatus where
  | draft
  | active
  | frozen
  | retired
  deriving DecidableEq, Repr

/-- Metadata associated with one account identifier. -/
structure AccountMetadata where
  accountKind : AccountClass
  status : AccountStatus
  network : NetworkId
  deriving DecidableEq, Repr

/-- Metadata associated with one asset identifier. -/
structure AssetMetadata (accountCount : Nat) where
  symbol : String
  decimals : Nat
  issuer : AccountId accountCount
  status : AssetStatus
  network : NetworkId
  deriving DecidableEq, Repr

/--
Number of integer base units in one whole unit of the asset.
This metadata does not select a production RFT decimal precision.
-/
def AssetMetadata.baseUnitsPerWhole
    {accountCount : Nat}
    (asset : AssetMetadata accountCount) : Nat :=
  10 ^ asset.decimals

theorem AssetMetadata.baseUnitsPerWhole_pos
    {accountCount : Nat}
    (asset : AssetMetadata accountCount) :
    0 < asset.baseUnitsPerWhole := by
  change 0 < (10 : Nat) ^ asset.decimals
  exact Nat.pow_pos (by decide)

/--
Total finite account catalog. Every identifier has exactly one metadata
record because metadata is a function keyed by AccountId.
-/
structure AccountRegistry (accountCount : Nat) where
  metadata : AccountId accountCount → AccountMetadata

namespace AccountRegistry

def classOf
    {accountCount : Nat}
    (registry : AccountRegistry accountCount)
    (account : AccountId accountCount) : AccountClass :=
  (registry.metadata account).accountKind

def isActive
    {accountCount : Nat}
    (registry : AccountRegistry accountCount)
    (account : AccountId accountCount) : Prop :=
  (registry.metadata account).status = .active

end AccountRegistry

/--
Total finite asset catalog tied to an account catalog.

Every asset issuer is an AccountId in the account universe. The proof
requires the issuer account and asset to declare the same network.
-/
structure AssetRegistry
    (accountCount assetCount : Nat)
    (accounts : AccountRegistry accountCount) where
  metadata : AssetId assetCount → AssetMetadata accountCount
  issuer_network_matches :
    ∀ asset,
      (metadata asset).network =
        (accounts.metadata (metadata asset).issuer).network

namespace AssetRegistry

def isActive
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts)
    (asset : AssetId assetCount) : Prop :=
  (registry.metadata asset).status = .active

/--
Registry-level issuance eligibility requires an active asset and an
active issuer account. This is additional to authorization and control.
-/
def issuanceEnabled
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts)
    (asset : AssetId assetCount) : Prop :=
  registry.isActive asset ∧
    AccountRegistry.isActive accounts (registry.metadata asset).issuer

theorem issuanceEnabled_requires_active_asset
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts)
    (asset : AssetId assetCount)
    (h : registry.issuanceEnabled asset) :
    registry.isActive asset :=
  h.1

theorem issuanceEnabled_requires_active_issuer
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts)
    (asset : AssetId assetCount)
    (h : registry.issuanceEnabled asset) :
    AccountRegistry.isActive accounts (registry.metadata asset).issuer :=
  h.2

theorem issuer_on_asset_network
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts)
    (asset : AssetId assetCount) :
    (registry.metadata asset).network =
      (accounts.metadata (registry.metadata asset).issuer).network :=
  registry.issuer_network_matches asset

end AssetRegistry

/-- Existing holdings model instantiated with typed finite identifiers. -/
abbrev TypedHoldingsState (accountCount assetCount : Nat) :=
  HoldingsState (AccountId accountCount) (AssetId assetCount)

/-- Existing signed ledger instantiated with typed identifiers. -/
abbrev TypedLedger (accountCount assetCount : Nat) :=
  Ledger (AccountId accountCount) (AssetId assetCount)

/-- The generic empty-state invariant also applies to typed accounts. -/
theorem typedEmptyHoldingsState_invariant
    (accountCount assetCount : Nat) :
    HoldingsInvariant
      (emptyHoldingsState
        (AccountId accountCount) (AssetId assetCount)) :=
  SIRM.emptyHoldingsState_invariant

end SIRM
