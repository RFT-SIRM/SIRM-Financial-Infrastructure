import SIRM.AuthorizedAssetMigration

/-!
# Replay-Protected Authorized Asset Migration

This module composes a per-principal sequential nonce with the existing
atomic authorized migration. A request is admitted only when its nonce is
the principal's exact next expected nonce. The financial migration and nonce
increment are returned as one abstract state transition.

This guard is scoped to this migration machine. It is not a global transaction
envelope, signature check, idempotent response cache, or persistent runtime
storage guarantee.
-/

namespace SIRM

/-- Migration state plus an independent next nonce for every principal. -/
structure ReplayProtectedAuthorizedAssetMigrationState
    (Principal : Type)
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (partition : AuthorizedAssetMigrationPartition registry)
    (LedgerAccount : Type) where
  migration : AuthorizedAssetMigrationState partition LedgerAccount
  nextNonce : Principal → Nat

/-- Every principal's migration nonce sequence starts at zero. -/
def initialReplayProtectedAuthorizedAssetMigrationState
    (Principal : Type)
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (partition : AuthorizedAssetMigrationPartition registry)
    {LedgerAccount : Type}
    (initialFinancial : FinancialState (AccountId accountCount)
      LedgerAccount (AssetId assetCount)) :
    ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount :=
  { migration := initialAuthorizedAssetMigrationState partition initialFinancial
    nextNonce := fun _ => 0 }

/-- Pure paired update: migration plus selected principal's nonce increment. -/
def applyReplayProtectedAuthorizedAssetMigration
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (partition : AuthorizedAssetMigrationPartition registry)
    (before : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount)
    (principal : Principal) (nonce sourceAmount : Nat) :
    ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount :=
  { migration := applyAuthorizedAssetMigration mapping counterpart partition
      before.migration sourceAmount
    nextNonce := fun candidate =>
      if candidate = principal then nonce + 1 else before.nextNonce candidate }

/-- Exact nonce, existing migration authorization, and one paired resulting state. -/
def ReplayProtectedAuthorizedAssetMigrationStep
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal : Principal) (nonce sourceAmount : Nat)
    (before after : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount) : Prop :=
  nonce = before.nextNonce principal ∧
  AuthorizedAssetMigrationStep control authority mapping counterpart hCounterpart
    partition principal sourceAmount before.migration after.migration ∧
  after = applyReplayProtectedAuthorizedAssetMigration Principal
    mapping counterpart partition before principal nonce sourceAmount

/-- A stale or future nonce cannot form an admitted step. -/
theorem replayProtectedAuthorizedAssetMigrationStep_reject_nonce_mismatch
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal : Principal) (nonce sourceAmount : Nat)
    (before after : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount)
    (hMismatch : nonce ≠ before.nextNonce principal) :
    ¬ ReplayProtectedAuthorizedAssetMigrationStep Principal control authority
      mapping counterpart hCounterpart partition principal nonce sourceAmount before after := by
  intro hStep
  exact hMismatch hStep.1

/-- An accepted step advances the selected principal's expected nonce by one. -/
theorem replayProtectedAuthorizedAssetMigrationStep_next_nonce
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal : Principal) (nonce sourceAmount : Nat)
    {before after : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount}
    (hStep : ReplayProtectedAuthorizedAssetMigrationStep Principal control authority
      mapping counterpart hCounterpart partition principal nonce sourceAmount before after) :
    after.nextNonce principal = nonce + 1 := by
  rcases hStep with ⟨_hExpected, _hMigration, rfl⟩
  simp [applyReplayProtectedAuthorizedAssetMigration]

/-- A principal's accepted migration does not change another principal's nonce. -/
theorem replayProtectedAuthorizedAssetMigrationStep_other_nonce
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal other : Principal) (nonce sourceAmount : Nat)
    {before after : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount}
    (hStep : ReplayProtectedAuthorizedAssetMigrationStep Principal control authority
      mapping counterpart hCounterpart partition principal nonce sourceAmount before after)
    (hOther : other ≠ principal) :
    after.nextNonce other = before.nextNonce other := by
  rcases hStep with ⟨_hExpected, _hMigration, rfl⟩
  simp [applyReplayProtectedAuthorizedAssetMigration, hOther]

/-- The wrapper preserves the complete pre-existing migration invariant. -/
def ReplayProtectedAuthorizedAssetMigrationInvariant
    (Principal : Type)
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (openingLedger : Ledger LedgerAccount (AssetId assetCount))
    {partition : AuthorizedAssetMigrationPartition registry}
    (state : ReplayProtectedAuthorizedAssetMigrationState
      Principal partition LedgerAccount) : Prop :=
  AuthorizedAssetMigrationInvariant mapping openingLedger state.migration

/-- Reachable machine with migration-scoped per-principal sequential nonces. -/
def replayProtectedAuthorizedAssetMigrationMachine
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (initialFinancial : FinancialState (AccountId accountCount)
      LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialFinancial) :
    VerifiedStateMachine
      (ReplayProtectedAuthorizedAssetMigrationState Principal partition LedgerAccount) :=
  { invariant := ReplayProtectedAuthorizedAssetMigrationInvariant
      Principal mapping initialFinancial.ledger
    initial := fun state => state =
      initialReplayProtectedAuthorizedAssetMigrationState Principal partition initialFinancial
    step := fun before after =>
      ∃ principal nonce sourceAmount,
        ReplayProtectedAuthorizedAssetMigrationStep Principal control authority
          mapping counterpart hCounterpart partition principal nonce sourceAmount before after
    initial_safe := by
      intro state hState
      cases hState
      exact ⟨⟨hInitial, by intro asset; rfl⟩,
        (AssetMigrationDustState.empty partition.route.rate partition).scaled_conservation⟩
    step_safe := by
      intro before after hBefore hStep
      rcases hStep with ⟨principal, nonce, sourceAmount, hStep⟩
      exact authorizedAssetMigrationStep_preserves_invariant
        control authority mapping counterpart hCounterpart partition
        principal sourceAmount initialFinancial.ledger hBefore hStep.2.1 }

/-- Every reachable replay-protected state retains the complete migration invariant. -/
theorem replayProtectedAuthorizedAssetMigrationInvariant_of_reachable
    (Principal : Type) [DecidableEq Principal]
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)] [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (initialFinancial : FinancialState (AccountId accountCount)
      LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialFinancial)
    {state : ReplayProtectedAuthorizedAssetMigrationState Principal partition LedgerAccount}
    (hReachable : Reachable
      (replayProtectedAuthorizedAssetMigrationMachine Principal control authority
        mapping counterpart hCounterpart partition initialFinancial hInitial) state) :
    ReplayProtectedAuthorizedAssetMigrationInvariant
      Principal mapping initialFinancial.ledger state := by
  exact invariant_of_reachable
    (replayProtectedAuthorizedAssetMigrationMachine Principal control authority
      mapping counterpart hCounterpart partition initialFinancial hInitial) hReachable

end SIRM
