import SIRM.Authorization

namespace SIRM

/--
An authority scope identifies the exact account operation.
A transfer is directional: source and destination both matter.
-/
inductive AuthorityScope (Account : Type) where
  | transfer (source destination : Account)
  | issue (recipient : Account)
  | burn (holder : Account)

/-- One grant binds a principal, exact scope, asset, and operation limit. -/
structure AuthorityGrant (Principal Account Asset : Type) where
  principal : Principal
  scope : AuthorityScope Account
  asset : Asset
  maxAmount : Nat

/--
A finite registry of grants.
Any two grants with the same principal/scope/asset key are equal.
Thus each key determines a unique grant value and operation limit.
-/
structure AuthorityRegistry (Principal Account Asset : Type) where
  grants : List (AuthorityGrant Principal Account Asset)
  unique_scope :
    ∀ {left right : AuthorityGrant Principal Account Asset},
      left ∈ grants →
      right ∈ grants →
      left.principal = right.principal →
      left.scope = right.scope →
      left.asset = right.asset →
      left = right

namespace AuthorityRegistry

/--
An operation is authorized exactly when a matching grant exists
and the requested amount is within its single-operation limit.
-/
def allows
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (principal : Principal)
    (scope : AuthorityScope Account)
    (asset : Asset)
    (amount : Nat) : Prop :=
  ∃ grant ∈ registry.grants,
    grant.principal = principal ∧
    grant.scope = scope ∧
    grant.asset = asset ∧
    amount ≤ grant.maxAmount

/-- Matching registry keys identify the same grant. -/
theorem unique_matching_grant
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    {principal : Principal}
    {scope : AuthorityScope Account}
    {asset : Asset}
    {left right : AuthorityGrant Principal Account Asset}
    (hLeftMem : left ∈ registry.grants)
    (hRightMem : right ∈ registry.grants)
    (hLeftPrincipal : left.principal = principal)
    (hRightPrincipal : right.principal = principal)
    (hLeftScope : left.scope = scope)
    (hRightScope : right.scope = scope)
    (hLeftAsset : left.asset = asset)
    (hRightAsset : right.asset = asset) :
    left = right := by
  exact registry.unique_scope
    hLeftMem hRightMem
    (hLeftPrincipal.trans hRightPrincipal.symm)
    (hLeftScope.trans hRightScope.symm)
    (hLeftAsset.trans hRightAsset.symm)

/-- A matching grant supplies the authorization witness. -/
theorem allows_of_mem
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (grant : AuthorityGrant Principal Account Asset)
    (principal : Principal)
    (scope : AuthorityScope Account)
    (asset : Asset)
    (amount : Nat)
    (hMem : grant ∈ registry.grants)
    (hPrincipal : grant.principal = principal)
    (hScope : grant.scope = scope)
    (hAsset : grant.asset = asset)
    (hLimit : amount ≤ grant.maxAmount) :
    allows registry principal scope asset amount := by
  exact ⟨grant, hMem, hPrincipal, hScope, hAsset, hLimit⟩

/--
Authorization is downward closed in the amount:
if a grant permits a larger operation, it permits every smaller one.
-/
theorem allows_amount_mono
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (principal : Principal)
    (scope : AuthorityScope Account)
    (asset : Asset)
    {smaller larger : Nat}
    (hSmaller : smaller ≤ larger)
    (hAllowed : allows registry principal scope asset larger) :
    allows registry principal scope asset smaller := by
  rcases hAllowed with
    ⟨grant, hMem, hPrincipal, hScope, hAsset, hLimit⟩
  exact ⟨grant, hMem, hPrincipal, hScope, hAsset,
    le_trans hSmaller hLimit⟩

/--
Translate the registry into the existing AuthorizationPolicy interface.

This first version is a static policy snapshot. The state argument is
unused; revocation and time-dependent policy changes are future work.
-/
def toAuthorizationPolicy
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset) :
    AuthorizationPolicy Principal Account Asset where
  mayTransfer := fun _ principal source destination asset amount =>
    allows registry principal
      (.transfer source destination) asset amount
  mayIssue := fun _ principal recipient asset amount =>
    allows registry principal
      (.issue recipient) asset amount
  mayBurn := fun _ principal holder asset amount =>
    allows registry principal
      (.burn holder) asset amount

@[simp]
theorem toAuthorizationPolicy_transfer
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (source destination : Account)
    (asset : Asset)
    (amount : Nat) :
    (toAuthorizationPolicy registry).mayTransfer
      state principal source destination asset amount ↔
    allows registry principal
      (.transfer source destination) asset amount := by
  rfl

@[simp]
theorem toAuthorizationPolicy_issue
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (recipient : Account)
    (asset : Asset)
    (amount : Nat) :
    (toAuthorizationPolicy registry).mayIssue
      state principal recipient asset amount ↔
    allows registry principal
      (.issue recipient) asset amount := by
  rfl

@[simp]
theorem toAuthorizationPolicy_burn
    {Principal Account Asset : Type}
    (registry : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (holder : Account)
    (asset : Asset)
    (amount : Nat) :
    (toAuthorizationPolicy registry).mayBurn
      state principal holder asset amount ↔
    allows registry principal
      (.burn holder) asset amount := by
  rfl

end AuthorityRegistry
end SIRM
