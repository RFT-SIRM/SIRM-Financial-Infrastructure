import SIRM.Authorization
import SIRM.StateMachine

/-!
# Authorized Holder State Machine

Only transitions carrying an explicit authorization witness are admitted.
The authorization policy is an explicit input; this module does not select
production ownership, keys, roles, signer thresholds, or governance rules.
-/

namespace SIRM

/-- The only admitted holder transitions are authorized transfer, issue, burn. -/
def AuthorizedHolderStep {Principal Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (before after : HoldingsState Account Asset) : Prop :=
  (∃ (principal : Principal) (source destination : Account)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayTransfer before principal source destination asset amount)
      (hAllowed : TransferAllowed before source destination asset amount),
      after = executeAuthorizedTransfer policy before principal
        source destination asset amount hAuthorized hAllowed)
  ∨
  (∃ (principal : Principal) (issuer recipient : Account)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayIssue before principal issuer recipient asset amount),
      after = executeAuthorizedIssue policy before principal issuer recipient
        asset amount hAuthorized)
  ∨
  (∃ (principal : Principal) (holder : Account)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayBurn before principal holder asset amount)
      (hEnough : (amount : Int) ≤ before.balance holder asset),
      after = executeAuthorizedBurn policy before principal holder
        asset amount hAuthorized hEnough)

/-- Every authorized transition preserves supply reconciliation and nonnegativity. -/
theorem authorizedHolderStep_preserves_invariant
    {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    {before after : HoldingsState Account Asset}
    (hBefore : HoldingsInvariant before)
    (hStep : AuthorizedHolderStep policy before after) :
    HoldingsInvariant after := by
  rcases hStep with hTransfer | hRest
  · rcases hTransfer with
      ⟨principal, source, destination, asset, amount,
        hAuthorized, hAllowed, hEq⟩
    subst after
    exact executeAuthorizedTransfer_preserves_invariant
      policy before hBefore principal source destination asset amount
      hAuthorized hAllowed
  · rcases hRest with hIssue | hBurn
    · rcases hIssue with
        ⟨principal, issuer, recipient, asset, amount, hAuthorized, hEq⟩
      subst after
      exact executeAuthorizedIssue_preserves_invariant
        policy before hBefore principal issuer recipient asset amount hAuthorized
    · rcases hBurn with
        ⟨principal, holder, asset, amount, hAuthorized, hEnough, hEq⟩
      subst after
      exact executeAuthorizedBurn_preserves_invariant
        policy before hBefore principal holder asset amount
        hAuthorized hEnough

/-- A machine starting at one invariant state and admitting only authorized steps. -/
def authorizedHolderMachine {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (initialState : HoldingsState Account Asset)
    (hInitial : HoldingsInvariant initialState) :
    VerifiedStateMachine (HoldingsState Account Asset) where
  invariant := HoldingsInvariant
  initial := fun state => state = initialState
  step := AuthorizedHolderStep policy
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact authorizedHolderStep_preserves_invariant policy hBefore hStep

/-- Every state reachable through authorized steps preserves the holdings invariant. -/
theorem holdingsInvariant_of_authorized_reachable
    {Principal Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (policy : AuthorizationPolicy Principal Account Asset)
    (initialState : HoldingsState Account Asset)
    (hInitial : HoldingsInvariant initialState)
    {state : HoldingsState Account Asset}
    (hReachable :
      Reachable (authorizedHolderMachine policy initialState hInitial) state) :
    HoldingsInvariant state := by
  exact invariant_of_reachable
    (authorizedHolderMachine policy initialState hInitial) hReachable

end SIRM
