import SIRM.AuthorityRegistry

/-!
# Static Account Control Registry

Account control is a finite relation independent of operation grants.
A transition requires both control of its source/issuer/holder account
and an exact authority grant.

This static snapshot does not establish legal title, cryptographic key
custody, signatures, revocation, or time-dependent control.
-/

namespace SIRM

structure AccountControlRegistry (Principal Account : Type) where
  entries : List (Principal × Account)

namespace AccountControlRegistry

def controls
    {Principal Account : Type}
    (registry : AccountControlRegistry Principal Account)
    (principal : Principal) (account : Account) : Prop :=
  (principal, account) ∈ registry.entries

end AccountControlRegistry

/--
Transfers check control of the source, issuance checks control of the
issuer, and burns check control of the holder. The recipient need not be
controlled by the actor; the exact issue grant binds the recipient.
-/
def toControlledAuthorizationPolicy
    {Principal Account Asset : Type}
    (control : AccountControlRegistry Principal Account)
    (authority : AuthorityRegistry Principal Account Asset) :
    AuthorizationPolicy Principal Account Asset where
  mayTransfer := fun _ principal source destination asset amount =>
    AccountControlRegistry.controls control principal source ∧
      AuthorityRegistry.allows authority principal
        (.transfer source destination) asset amount
  mayIssue := fun _ principal issuer recipient asset amount =>
    AccountControlRegistry.controls control principal issuer ∧
      AuthorityRegistry.allows authority principal
        (.issue issuer recipient) asset amount
  mayBurn := fun _ principal holder asset amount =>
    AccountControlRegistry.controls control principal holder ∧
      AuthorityRegistry.allows authority principal
        (.burn holder) asset amount

@[simp]
theorem toControlledAuthorizationPolicy_transfer
    {Principal Account Asset : Type}
    (control : AccountControlRegistry Principal Account)
    (authority : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (source destination : Account)
    (asset : Asset) (amount : Nat) :
    (toControlledAuthorizationPolicy control authority).mayTransfer
      state principal source destination asset amount ↔
    AccountControlRegistry.controls control principal source ∧
      AuthorityRegistry.allows authority principal
        (.transfer source destination) asset amount := by
  rfl

@[simp]
theorem toControlledAuthorizationPolicy_issue
    {Principal Account Asset : Type}
    (control : AccountControlRegistry Principal Account)
    (authority : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (issuer recipient : Account)
    (asset : Asset) (amount : Nat) :
    (toControlledAuthorizationPolicy control authority).mayIssue
      state principal issuer recipient asset amount ↔
    AccountControlRegistry.controls control principal issuer ∧
      AuthorityRegistry.allows authority principal
        (.issue issuer recipient) asset amount := by
  rfl

@[simp]
theorem toControlledAuthorizationPolicy_burn
    {Principal Account Asset : Type}
    (control : AccountControlRegistry Principal Account)
    (authority : AuthorityRegistry Principal Account Asset)
    (state : HoldingsState Account Asset)
    (principal : Principal)
    (holder : Account)
    (asset : Asset) (amount : Nat) :
    (toControlledAuthorizationPolicy control authority).mayBurn
      state principal holder asset amount ↔
    AccountControlRegistry.controls control principal holder ∧
      AuthorityRegistry.allows authority principal
        (.burn holder) asset amount := by
  rfl

end SIRM
