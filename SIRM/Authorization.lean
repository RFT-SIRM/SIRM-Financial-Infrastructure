import SIRM.Holdings

/-!
# Authorization Gates for Holder Operations

This module defines an abstract authorization boundary for holder transfers,
issuance, and burns. It deliberately does not choose account ownership,
cryptographic keys, role assignments, signer thresholds, or governance rules.
Those remain explicit policy inputs for a later protocol decision.
-/

namespace SIRM

/--
An authorization policy supplies state-dependent permission relations for
the three holder operations. `Principal` is an abstract actor identity;
it is not itself a cryptographic key or proof of key custody.
-/
structure AuthorizationPolicy (Principal Account Asset : Type) where
  mayTransfer :
    HoldingsState Account Asset → Principal →
      Account → Account → Asset → Nat → Prop
  mayIssue :
    HoldingsState Account Asset → Principal →
      Account → Asset → Nat → Prop
  mayBurn :
    HoldingsState Account Asset → Principal →
      Account → Asset → Nat → Prop

/--
A transfer requires two independent witnesses: policy authorization and
the existing funding/self-transfer precondition.
-/
def executeAuthorizedTransfer {Principal Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal) (source destination : Account)
    (asset : Asset) (amount : Nat)
    (_hAuthorized :
      policy.mayTransfer state principal source destination asset amount)
    (hAllowed : TransferAllowed state source destination asset amount) :
    HoldingsState Account Asset :=
  executeTransfer state source destination asset amount hAllowed

/-- An authorized issuance requires an explicit policy witness. -/
def executeAuthorizedIssue {Principal Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal) (recipient : Account)
    (asset : Asset) (amount : Nat)
    (_hAuthorized :
      policy.mayIssue state principal recipient asset amount) :
    HoldingsState Account Asset :=
  issueToHolder state recipient asset amount

/-- An authorized burn requires both policy permission and sufficient funds. -/
def executeAuthorizedBurn {Principal Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal) (holder : Account)
    (asset : Asset) (amount : Nat)
    (_hAuthorized :
      policy.mayBurn state principal holder asset amount)
    (hEnough : (amount : Int) ≤ state.balance holder asset) :
    HoldingsState Account Asset :=
  executeBurn state holder asset amount hEnough

/-- An authorized transfer preserves the holdings/supply invariant. -/
theorem executeAuthorizedTransfer_preserves_invariant
    {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (principal : Principal) (source destination : Account)
    (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer state principal source destination asset amount)
    (hAllowed : TransferAllowed state source destination asset amount) :
    HoldingsInvariant
      (executeAuthorizedTransfer policy state principal source destination
        asset amount hAuthorized hAllowed) := by
  exact executeTransfer_preserves_invariant state hInvariant
    source destination asset amount hAllowed

/-- An authorized issuance preserves the holdings/supply invariant. -/
theorem executeAuthorizedIssue_preserves_invariant
    {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (principal : Principal) (recipient : Account)
    (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayIssue state principal recipient asset amount) :
    HoldingsInvariant
      (executeAuthorizedIssue policy state principal recipient
        asset amount hAuthorized) := by
  exact issueToHolder_preserves_invariant state hInvariant
    recipient asset amount

/-- An authorized burn preserves the holdings/supply invariant. -/
theorem executeAuthorizedBurn_preserves_invariant
    {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (principal : Principal) (holder : Account)
    (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayBurn state principal holder asset amount)
    (hEnough : (amount : Int) ≤ state.balance holder asset) :
    HoldingsInvariant
      (executeAuthorizedBurn policy state principal holder
        asset amount hAuthorized hEnough) := by
  exact executeBurn_preserves_invariant state hInvariant
    holder asset amount hEnough

end SIRM
