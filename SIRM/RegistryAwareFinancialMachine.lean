import SIRM.AuthorizedFinancialMachine
import SIRM.TypedRegistry

/-!
# Registry-Aware Authorized Financial Machine

The existing authority-grant and account-control policy remains mandatory.
This adapter adds typed asset-registry eligibility to issuance only: an issue
must target an active asset whose issuer account is active. Transfer and burn
authorization predicates are preserved unchanged.
-/

namespace SIRM

/--
Compose an existing authorization policy with the typed asset registry.
Issuance requires both the original policy and registry-level eligibility.
Transfers and burns retain exactly the original policy predicates.
-/
def withAssetRegistryIssuanceGate
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts) :
    AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount) where
  mayTransfer := policy.mayTransfer
  mayIssue := fun state principal issuer recipient asset amount =>
    policy.mayIssue state principal issuer recipient asset amount ∧
      registry.issuanceEnabled asset
  mayBurn := policy.mayBurn

@[simp]
theorem withAssetRegistryIssuanceGate_mayTransfer_iff
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts)
    (state : HoldingsState (AccountId accountCount) (AssetId assetCount))
    (principal : Principal)
    (source destination : AccountId accountCount)
    (asset : AssetId assetCount) (amount : Nat) :
    (withAssetRegistryIssuanceGate policy registry).mayTransfer
      state principal source destination asset amount ↔
    policy.mayTransfer state principal source destination asset amount :=
  Iff.rfl

@[simp]
theorem withAssetRegistryIssuanceGate_mayIssue_iff
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts)
    (state : HoldingsState (AccountId accountCount) (AssetId assetCount))
    (principal : Principal)
    (issuer recipient : AccountId accountCount)
    (asset : AssetId assetCount) (amount : Nat) :
    (withAssetRegistryIssuanceGate policy registry).mayIssue
      state principal issuer recipient asset amount ↔
    policy.mayIssue state principal issuer recipient asset amount ∧
      registry.issuanceEnabled asset :=
  Iff.rfl

@[simp]
theorem withAssetRegistryIssuanceGate_mayBurn_iff
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts)
    (state : HoldingsState (AccountId accountCount) (AssetId assetCount))
    (principal : Principal)
    (holder : AccountId accountCount)
    (asset : AssetId assetCount) (amount : Nat) :
    (withAssetRegistryIssuanceGate policy registry).mayBurn
      state principal holder asset amount ↔
    policy.mayBurn state principal holder asset amount :=
  Iff.rfl

/--
The registry-aware machine reuses the existing paired financial transition
and its conservation invariant. Only its issuance authorization gate changes.
-/
def registryAwareAuthorizedFinancialMachine
    {Principal LedgerAccount : Type}
    {accountCount assetCount : Nat}
    [Fintype (AccountId accountCount)]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts)
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialState) :
    VerifiedStateMachine
      (FinancialState
        (AccountId accountCount) LedgerAccount (AssetId assetCount)) :=
  authorizedFinancialMachineWithConservation
    (withAssetRegistryIssuanceGate policy registry)
    mapping counterpart initialState hInitial

/-- Reachable states preserve the full combined financial invariant. -/
theorem registryAwareFinancialConservationInvariant_of_reachable
    {Principal LedgerAccount : Type}
    {accountCount assetCount : Nat}
    [Fintype (AccountId accountCount)]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    {accounts : AccountRegistry accountCount}
    (policy : AuthorizationPolicy Principal
      (AccountId accountCount) (AssetId assetCount))
    (registry : AssetRegistry accountCount assetCount accounts)
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialState)
    {state : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount)}
    (hReachable :
      Reachable
        (registryAwareAuthorizedFinancialMachine
          policy registry mapping counterpart initialState hInitial) state) :
    FinancialConservationInvariant mapping initialState.ledger state := by
  exact financialConservationInvariant_of_authorized_reachable
    (withAssetRegistryIssuanceGate policy registry)
    mapping counterpart initialState hInitial hReachable

end SIRM
