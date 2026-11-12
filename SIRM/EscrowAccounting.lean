import SIRM.AuthorizedFinancialMachine

/-!
# Authorized Escrow Accounting

This first escrow model uses one dedicated holder account and one escrow
record. Opening moves already-issued units from the depositor to the escrow
account. Release transfers exactly those units to the recorded beneficiary;
cancellation returns them to the depositor. Each leg is an ordinary
authorization-gated holder transfer paired with its balanced GL journal.

The escrow vault is part of the holder universe, so escrowed units remain
included in the existing supply reconciliation. No units are minted, burned,
or represented a second time. This first block deliberately does not model
multiple concurrent escrow IDs, dispute resolution, wall-clock deadline binding,
expiry scheduler liveness, external settlement evidence, or global transaction
idempotency. Time-lock safety is specified separately in `EscrowTimeLocks`.
-/

namespace SIRM

/-- The lifecycle of the single escrow record. A terminal record cannot reopen. -/
inductive EscrowPhase
  | ready
  | pending
  | released
  | cancelled
  | expired
  deriving DecidableEq, Repr

/-- Immutable terms and current lifecycle phase of one escrow. -/
structure EscrowRecord (Holder Asset : Type) where
  depositor : Holder
  beneficiary : Holder
  asset : Asset
  amount : Nat
  phase : EscrowPhase

/-- Holder balances, the signed GL, and one escrow record. -/
structure EscrowFinancialState (Holder LedgerAccount Asset : Type) where
  financial : FinancialState Holder LedgerAccount Asset
  record : EscrowRecord Holder Asset

/--
The escrow invariant combines the complete existing financial invariant
with exact vault backing. The dedicated vault holds exactly the recorded
amount of the escrow asset while pending, and zero units of every asset in
all other phases. A pending escrow must have a positive amount and a vault
distinct from its depositor and beneficiary.
-/
def EscrowFinancialInvariant
    {Holder LedgerAccount Asset : Type}
    [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (escrowAccount : Holder)
    (state : EscrowFinancialState Holder LedgerAccount Asset) : Prop :=
  FinancialConservationInvariant mapping openingLedger state.financial ∧
    (∀ asset,
      state.financial.holdings.balance escrowAccount asset =
        if state.record.phase = EscrowPhase.pending ∧
            asset = state.record.asset
        then (state.record.amount : Int) else 0) ∧
    (state.record.phase = EscrowPhase.pending →
      escrowAccount ≠ state.record.depositor ∧
      escrowAccount ≠ state.record.beneficiary ∧
      0 < state.record.amount)

/--
Escrow permissions are separate from ordinary transfer authorization.
A caller must satisfy both the existing transfer policy (which can combine
account control and an exact transfer grant) and the escrow-specific policy.
Timeout refunds additionally require the dedicated `mayExpireEscrow` permission;
voluntary cancellation does not grant expiry authority by itself.
-/
structure EscrowAuthorizationPolicy (Principal Holder Asset : Type) where
  mayOpenEscrow :
    HoldingsState Holder Asset → Principal →
      Holder → Holder → Holder → Asset → Nat → Prop
  mayReleaseEscrow :
    HoldingsState Holder Asset → Principal →
      Holder → Holder → Holder → Asset → Nat → Prop
  mayCancelEscrow :
    HoldingsState Holder Asset → Principal →
      Holder → Holder → Holder → Asset → Nat → Prop
  mayExpireEscrow :
    HoldingsState Holder Asset → Principal →
      Holder → Holder → Holder → Asset → Nat → Prop

/-- Lock already-issued units by transferring them to the escrow vault. -/
def openEscrowFinancialState
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before : EscrowFinancialState Holder LedgerAccount Asset)
    (principal : Principal) (depositor beneficiary : Holder)
    (asset : Asset) (amount : Nat)
    (hTransfer :
      transferPolicy.mayTransfer before.financial.holdings principal
        depositor escrowAccount asset amount)
    (hAllowed :
      TransferAllowed before.financial.holdings depositor escrowAccount
        asset amount) : EscrowFinancialState Holder LedgerAccount Asset :=
  { financial :=
      { holdings := executeAuthorizedTransfer transferPolicy
          before.financial.holdings principal depositor escrowAccount
          asset amount hTransfer hAllowed
        ledger := postJournal before.financial.ledger
          (holderTransferJournal mapping depositor escrowAccount asset amount) }
    record :=
      { depositor := depositor
        beneficiary := beneficiary
        asset := asset
        amount := amount
        phase := EscrowPhase.pending } }

/-- Release the pending amount to the beneficiary fixed in the escrow record. -/
def releaseEscrowFinancialState
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before : EscrowFinancialState Holder LedgerAccount Asset)
    (principal : Principal)
    (hTransfer :
      transferPolicy.mayTransfer before.financial.holdings principal
        escrowAccount before.record.beneficiary before.record.asset
        before.record.amount)
    (hAllowed :
      TransferAllowed before.financial.holdings escrowAccount
        before.record.beneficiary before.record.asset before.record.amount) :
    EscrowFinancialState Holder LedgerAccount Asset :=
  { financial :=
      { holdings := executeAuthorizedTransfer transferPolicy
          before.financial.holdings principal escrowAccount
          before.record.beneficiary before.record.asset before.record.amount
          hTransfer hAllowed
        ledger := postJournal before.financial.ledger
          (holderTransferJournal mapping escrowAccount
            before.record.beneficiary before.record.asset before.record.amount) }
    record := { before.record with phase := EscrowPhase.released } }

/-- Cancel the pending escrow and return its exact amount to the depositor. -/
def cancelEscrowFinancialState
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before : EscrowFinancialState Holder LedgerAccount Asset)
    (principal : Principal)
    (hTransfer :
      transferPolicy.mayTransfer before.financial.holdings principal
        escrowAccount before.record.depositor before.record.asset
        before.record.amount)
    (hAllowed :
      TransferAllowed before.financial.holdings escrowAccount
        before.record.depositor before.record.asset before.record.amount) :
    EscrowFinancialState Holder LedgerAccount Asset :=
  { financial :=
      { holdings := executeAuthorizedTransfer transferPolicy
          before.financial.holdings principal escrowAccount
          before.record.depositor before.record.asset before.record.amount
          hTransfer hAllowed
        ledger := postJournal before.financial.ledger
          (holderTransferJournal mapping escrowAccount
            before.record.depositor before.record.asset before.record.amount) }
    record := { before.record with phase := EscrowPhase.cancelled } }

/--
An authorized holder transfer and its corresponding balanced journal
preserve the complete financial invariant and aggregate signed GL balance.
-/
theorem escrowTransferFinancial_preserves_conservation
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (before : FinancialState Holder LedgerAccount Asset)
    (hBefore : FinancialConservationInvariant mapping openingLedger before)
    (principal : Principal) (source destination : Holder)
    (asset : Asset) (amount : Nat)
    (hTransfer :
      transferPolicy.mayTransfer before.holdings principal
        source destination asset amount)
    (hAllowed : TransferAllowed before.holdings source destination asset amount) :
    FinancialConservationInvariant mapping openingLedger
      { holdings := executeAuthorizedTransfer transferPolicy before.holdings
          principal source destination asset amount hTransfer hAllowed
        ledger := postJournal before.ledger
          (holderTransferJournal mapping source destination asset amount) } := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact executeAuthorizedTransfer_preserves_invariant
        transferPolicy before.holdings hBefore.1.1
        principal source destination asset amount hTransfer hAllowed
    · exact holderSubledgerAgreement_transfer mapping before.holdings
        before.ledger hBefore.1.2 source destination asset amount hAllowed
  · intro queryAsset
    calc
      totalSignedBalance
          (postJournal before.ledger
            (holderTransferJournal mapping source destination asset amount))
          queryAsset =
        totalSignedBalance before.ledger queryAsset :=
          totalSignedBalance_postJournal before.ledger
            (holderTransferJournal mapping source destination asset amount)
            queryAsset
      _ = totalSignedBalance openingLedger queryAsset := hBefore.2 queryAsset

/--
Opening is admitted only from the `ready` phase, so this escrow record cannot
be reused after release or cancellation. Both normal transfer authorization
and escrow-specific authorization are required.
-/
def EscrowOpenStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before after : EscrowFinancialState Holder LedgerAccount Asset) : Prop :=
  ∃ (principal : Principal) (depositor beneficiary : Holder)
      (asset : Asset) (amount : Nat)
      (_hReady : before.record.phase = EscrowPhase.ready)
      (_hEscrowNotDepositor : escrowAccount ≠ depositor)
      (_hEscrowNotBeneficiary : escrowAccount ≠ beneficiary)
      (_hPositive : 0 < amount)
      (hTransfer :
        transferPolicy.mayTransfer before.financial.holdings principal
          depositor escrowAccount asset amount)
      (_hEscrow :
        escrowPolicy.mayOpenEscrow before.financial.holdings principal
          depositor beneficiary escrowAccount asset amount)
      (hAllowed :
        TransferAllowed before.financial.holdings depositor escrowAccount
          asset amount),
      after = openEscrowFinancialState transferPolicy mapping escrowAccount
        before principal depositor beneficiary asset amount hTransfer hAllowed

/-- Release requires a pending record and both ordinary and escrow permissions. -/
def EscrowReleaseStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before after : EscrowFinancialState Holder LedgerAccount Asset) : Prop :=
  ∃ (principal : Principal)
      (_hPending : before.record.phase = EscrowPhase.pending)
      (hTransfer :
        transferPolicy.mayTransfer before.financial.holdings principal
          escrowAccount before.record.beneficiary before.record.asset
          before.record.amount)
      (_hEscrow :
        escrowPolicy.mayReleaseEscrow before.financial.holdings principal
          escrowAccount before.record.depositor before.record.beneficiary
          before.record.asset before.record.amount)
      (hAllowed :
        TransferAllowed before.financial.holdings escrowAccount
          before.record.beneficiary before.record.asset before.record.amount),
      after = releaseEscrowFinancialState transferPolicy mapping escrowAccount
        before principal hTransfer hAllowed

/-- Cancellation requires a pending record and both ordinary and escrow permissions. -/
def EscrowCancelStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before after : EscrowFinancialState Holder LedgerAccount Asset) : Prop :=
  ∃ (principal : Principal)
      (_hPending : before.record.phase = EscrowPhase.pending)
      (hTransfer :
        transferPolicy.mayTransfer before.financial.holdings principal
          escrowAccount before.record.depositor before.record.asset
          before.record.amount)
      (_hEscrow :
        escrowPolicy.mayCancelEscrow before.financial.holdings principal
          escrowAccount before.record.depositor before.record.beneficiary
          before.record.asset before.record.amount)
      (hAllowed :
        TransferAllowed before.financial.holdings escrowAccount
          before.record.depositor before.record.asset before.record.amount),
      after = cancelEscrowFinancialState transferPolicy mapping escrowAccount
        before principal hTransfer hAllowed

/-- The complete first-version escrow transition relation. -/
def EscrowFinancialStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (escrowAccount : Holder)
    (before after : EscrowFinancialState Holder LedgerAccount Asset) : Prop :=
  EscrowOpenStep transferPolicy escrowPolicy mapping escrowAccount before after ∨
    EscrowReleaseStep transferPolicy escrowPolicy mapping escrowAccount before after ∨
    EscrowCancelStep transferPolicy escrowPolicy mapping escrowAccount before after

/-- Every open, release, or cancel step preserves the escrow and financial invariants. -/
theorem escrowFinancialStep_preserves_invariant
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (escrowAccount : Holder)
    {before after : EscrowFinancialState Holder LedgerAccount Asset}
    (hBefore : EscrowFinancialInvariant mapping openingLedger escrowAccount before)
    (hStep : EscrowFinancialStep transferPolicy escrowPolicy mapping
      escrowAccount before after) :
    EscrowFinancialInvariant mapping openingLedger escrowAccount after := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with
      ⟨principal, depositor, beneficiary, asset, amount,
        hReady, hEscrowNotDepositor, hEscrowNotBeneficiary, hPositive,
        hTransfer, hEscrow, hAllowed, hEq⟩
    subst after
    refine ⟨?_, ?_, ?_⟩
    · exact escrowTransferFinancial_preserves_conservation
        transferPolicy mapping openingLedger before.financial hBefore.1
        principal depositor escrowAccount asset amount hTransfer hAllowed
    · intro currentAsset
      by_cases hAsset : currentAsset = asset
      · subst currentAsset
        have hVaultZero :
            before.financial.holdings.balance escrowAccount asset = 0 := by
          simpa [hReady] using hBefore.2.1 asset
        simp [openEscrowFinancialState, executeAuthorizedTransfer,
          executeTransfer, transferBetweenHolders, hEscrowNotDepositor, hVaultZero]
      · have hVaultZero :
            before.financial.holdings.balance escrowAccount currentAsset = 0 := by
          simpa [hReady, hAsset] using hBefore.2.1 currentAsset
        simp [openEscrowFinancialState, executeAuthorizedTransfer,
          executeTransfer, transferBetweenHolders, hAsset, hVaultZero]
    · intro _
      exact ⟨hEscrowNotDepositor, hEscrowNotBeneficiary, hPositive⟩
  · rcases hRest with hRelease | hCancel
    · rcases hRelease with
        ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
      subst after
      have hDistinct := hBefore.2.2 hPending
      have hVaultAmount :
          before.financial.holdings.balance escrowAccount before.record.asset =
            (before.record.amount : Int) := by
        simpa [hPending] using hBefore.2.1 before.record.asset
      refine ⟨?_, ?_, ?_⟩
      · exact escrowTransferFinancial_preserves_conservation
          transferPolicy mapping openingLedger before.financial hBefore.1
          principal escrowAccount before.record.beneficiary before.record.asset
          before.record.amount hTransfer hAllowed
      · intro currentAsset
        by_cases hAsset : currentAsset = before.record.asset
        · subst currentAsset
          simp [releaseEscrowFinancialState, executeAuthorizedTransfer,
            executeTransfer, transferBetweenHolders, hDistinct.2.1, hVaultAmount]
        · have hVaultZero :
              before.financial.holdings.balance escrowAccount currentAsset = 0 := by
            simpa [hPending, hAsset] using hBefore.2.1 currentAsset
          simp [releaseEscrowFinancialState, executeAuthorizedTransfer,
            executeTransfer, transferBetweenHolders, hAsset, hVaultZero]
      · intro hPendingAfter
        cases hPendingAfter
    · rcases hCancel with
        ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
      subst after
      have hDistinct := hBefore.2.2 hPending
      have hVaultAmount :
          before.financial.holdings.balance escrowAccount before.record.asset =
            (before.record.amount : Int) := by
        simpa [hPending] using hBefore.2.1 before.record.asset
      refine ⟨?_, ?_, ?_⟩
      · exact escrowTransferFinancial_preserves_conservation
          transferPolicy mapping openingLedger before.financial hBefore.1
          principal escrowAccount before.record.depositor before.record.asset
          before.record.amount hTransfer hAllowed
      · intro currentAsset
        by_cases hAsset : currentAsset = before.record.asset
        · subst currentAsset
          simp [cancelEscrowFinancialState, executeAuthorizedTransfer,
            executeTransfer, transferBetweenHolders, hDistinct.1, hVaultAmount]
        · have hVaultZero :
              before.financial.holdings.balance escrowAccount currentAsset = 0 := by
            simpa [hPending, hAsset] using hBefore.2.1 currentAsset
          simp [cancelEscrowFinancialState, executeAuthorizedTransfer,
            executeTransfer, transferBetweenHolders, hAsset, hVaultZero]
      · intro hPendingAfter
        cases hPendingAfter

/-- A verified machine whose only financial operations are authorized escrow transitions. -/
def escrowFinancialMachine
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (escrowAccount : Holder)
    (initialState : EscrowFinancialState Holder LedgerAccount Asset)
    (hInitial : EscrowFinancialInvariant mapping openingLedger escrowAccount initialState) :
    VerifiedStateMachine (EscrowFinancialState Holder LedgerAccount Asset) where
  invariant := EscrowFinancialInvariant mapping openingLedger escrowAccount
  initial := fun state => state = initialState
  step := EscrowFinancialStep transferPolicy escrowPolicy mapping escrowAccount
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact escrowFinancialStep_preserves_invariant
      transferPolicy escrowPolicy mapping openingLedger escrowAccount hBefore hStep

/-- Every reachable escrow state retains exact vault backing and full financial reconciliation. -/
theorem escrowFinancialInvariant_of_reachable
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (escrowAccount : Holder)
    (initialState : EscrowFinancialState Holder LedgerAccount Asset)
    (hInitial : EscrowFinancialInvariant mapping openingLedger escrowAccount initialState)
    {state : EscrowFinancialState Holder LedgerAccount Asset}
    (hReachable :
      Reachable (escrowFinancialMachine transferPolicy escrowPolicy mapping
        openingLedger escrowAccount initialState hInitial) state) :
    EscrowFinancialInvariant mapping openingLedger escrowAccount state :=
  invariant_of_reachable
    (escrowFinancialMachine transferPolicy escrowPolicy mapping
      openingLedger escrowAccount initialState hInitial) hReachable

end SIRM
