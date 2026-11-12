import SIRM.EscrowFinancialIntegration

/-!
# Time-Locked Financial Escrow

This layer adds discrete, monotone time to the financially integrated
multi-record escrow machine. Each escrow ID is assigned an absolute deadline
by an immutable `EscrowId → Nat` schedule supplied to the verified machine.
Opening and ordinary release/voluntary cancellation are admitted only before
the selected ID's deadline. At or after the deadline, a separate expiry step
may return the still-pending amount to its depositor, subject to a dedicated
expiry permission and the ordinary transfer permission.

All financial movement still goes through the integrated escrow operations.
Consequently, expiry preserves the existing equality between the vault-holder
balance, the aggregate pending liability, and the mapped GL subledger.

The clock is an abstract discrete `Nat`, not a wall-clock oracle. The model
proves safety and deadline gating; it does not prove that an external scheduler
will invoke expiry, so timeout liveness and automatic execution remain outside
this specification. The per-ID deadline schedule is fixed for each verified
machine; dynamically persisting expiry terms inside records is a later runtime
refinement concern.
-/

namespace SIRM

/-- Terminal registry update reserved for timeout expiry (not voluntary cancel). -/
def escrowRegistryExpire
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) :
    EscrowRegistry EscrowId Holder Asset :=
  ⟨fun query =>
    if query = id then some { record with phase := EscrowPhase.expired }
    else before.records query⟩

/-- Expiring a pending registry record preserves registry validity. -/
theorem escrowRegistryExpire_preserves_invariant
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (hBefore : EscrowRegistryInvariant before)
    (hRecord : before.records id = some record)
    (_hPending : record.phase = EscrowPhase.pending) :
    EscrowRegistryInvariant (escrowRegistryExpire before id record) := by
  intro query found hFound
  by_cases hQuery : query = id
  · subst query
    have hSome :
        some { record with phase := EscrowPhase.expired } = some found := by
      simpa [escrowRegistryExpire] using hFound
    have hRecord' : { record with phase := EscrowPhase.expired } = found :=
      Option.some.inj hSome
    subst found
    exact ⟨by simp, (hBefore id record hRecord).2⟩
  · have hOld : before.records query = some found := by
      simpa [escrowRegistryExpire, hQuery] using hFound
    exact hBefore query found hOld

/-- Expiry changes only the selected ID; all other registry entries are framed. -/
theorem escrowRegistryExpire_other
    {EscrowId Holder Asset : Type} [DecidableEq EscrowId]
    (before : EscrowRegistry EscrowId Holder Asset)
    (id other : EscrowId) (record : EscrowRecord Holder Asset)
    (hDifferent : other ≠ id) :
    (escrowRegistryExpire before id record).records other = before.records other := by
  simp [escrowRegistryExpire, hDifferent]

/-- Expiry removes exactly the timed-out amount from the pending aggregate. -/
theorem pooledEscrowReserve_expire
    {EscrowId Holder Asset : Type}
    [Fintype EscrowId] [DecidableEq EscrowId] [DecidableEq Asset]
    (registry : EscrowRegistry EscrowId Holder Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset) (asset : Asset)
    (hRecord : registry.records id = some record)
    (hPending : record.phase = EscrowPhase.pending) :
    pooledEscrowReserve (escrowRegistryExpire registry id record) asset =
      pooledEscrowReserve registry asset -
        (if record.asset = asset then (record.amount : Int) else 0) := by
  classical
  unfold pooledEscrowReserve
  calc
    (∑ query : EscrowId,
        pooledEscrowContribution (escrowRegistryExpire registry id record) query asset) =
      ∑ query : EscrowId,
        (pooledEscrowContribution registry query asset -
          (if query = id then
            (if record.asset = asset then (record.amount : Int) else 0)
           else 0)) := by
        apply Finset.sum_congr rfl
        intro query _
        by_cases hQuery : query = id
        · subst query
          simp [pooledEscrowContribution, escrowRegistryExpire, hRecord, hPending]
        · simp [pooledEscrowContribution, escrowRegistryExpire, hQuery]
    _ = (∑ query : EscrowId, pooledEscrowContribution registry query asset) -
        (if record.asset = asset then (record.amount : Int) else 0) := by
          rw [Finset.sum_sub_distrib]
          simp

/-- Financial escrow state paired with a monotone discrete clock. -/
structure EscrowTimeLockedFinancialRegistryState
    (EscrowId Holder LedgerAccount Asset : Type) where
  escrow : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset
  currentTime : Nat

/-- The time-locked wrapper reuses the complete integrated escrow invariant. -/
def EscrowTimeLockedFinancialRegistryInvariant
    {EscrowId Holder LedgerAccount Asset : Type}
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (state : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder state.escrow

/-- Empty timed registry at a caller-selected initial discrete time. -/
def emptyEscrowTimeLockedFinancialRegistryState
    {EscrowId Holder LedgerAccount Asset : Type}
    (financial : FinancialState Holder LedgerAccount Asset)
    (currentTime : Nat) :
    EscrowTimeLockedFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { escrow := emptyEscrowFinancialRegistryState financial
    currentTime := currentTime }

/--
Opening a fresh ID requires a positive funded escrow and a deadline strictly
later than the current time. The deadline itself is an immutable machine
parameter indexed by escrow ID.
-/
def EscrowTimeLockedOpenStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (principal : Principal) (depositor beneficiary : Holder)
      (asset : Asset) (amount : Nat),
    before.escrow.registry.records id = none ∧
    before.currentTime < expiresAt id ∧
    vaultHolder ≠ depositor ∧
    vaultHolder ≠ beneficiary ∧
    0 < amount ∧
    ∃ (hTransfer : policy.mayTransfer before.escrow.financial.holdings principal
        depositor vaultHolder asset amount)
      (_hEscrow : escrowPolicy.mayOpenEscrow before.escrow.financial.holdings
        principal depositor beneficiary vaultHolder asset amount)
      (hAllowed : TransferAllowed before.escrow.financial.holdings
        depositor vaultHolder asset amount),
      after =
        { escrow := escrowFinancialRegistryOpen policy mapping vaultHolder
            before.escrow id principal depositor beneficiary asset amount
            hTransfer hAllowed
          currentTime := before.currentTime }

/-- Release is admitted only strictly before the record's fixed deadline. -/
def EscrowTimeLockedReleaseStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (record : EscrowRecord Holder Asset) (principal : Principal),
    before.escrow.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    before.currentTime < expiresAt id ∧
    ∃ (hTransfer : policy.mayTransfer before.escrow.financial.holdings principal
        vaultHolder record.beneficiary record.asset record.amount)
      (_hEscrow : escrowPolicy.mayReleaseEscrow before.escrow.financial.holdings
        principal vaultHolder record.depositor record.beneficiary record.asset
        record.amount)
      (hAllowed : TransferAllowed before.escrow.financial.holdings
        vaultHolder record.beneficiary record.asset record.amount),
      after =
        { escrow := escrowFinancialRegistryRelease policy mapping vaultHolder
            before.escrow id record principal hTransfer hAllowed
          currentTime := before.currentTime }

/-- Voluntary cancellation is also restricted to the pre-deadline interval. -/
def EscrowTimeLockedCancelStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (record : EscrowRecord Holder Asset) (principal : Principal),
    before.escrow.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    before.currentTime < expiresAt id ∧
    ∃ (hTransfer : policy.mayTransfer before.escrow.financial.holdings principal
        vaultHolder record.depositor record.asset record.amount)
      (_hEscrow : escrowPolicy.mayCancelEscrow before.escrow.financial.holdings
        principal vaultHolder record.depositor record.beneficiary record.asset
        record.amount)
      (hAllowed : TransferAllowed before.escrow.financial.holdings
        vaultHolder record.depositor record.asset record.amount),
      after =
        { escrow := escrowFinancialRegistryCancel policy mapping vaultHolder
            before.escrow id record principal hTransfer hAllowed
          currentTime := before.currentTime }

/-- Apply the financial refund and record a distinct expired terminal status. -/
def escrowFinancialRegistryExpire
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (principal : Principal)
    (hAuthorized : policy.mayTransfer before.financial.holdings principal
      vaultHolder record.depositor record.asset record.amount)
    (hAllowed : TransferAllowed before.financial.holdings vaultHolder
      record.depositor record.asset record.amount) :
    EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { financial := escrowFinancialRegistryTransferFinancial policy mapping
      before.financial principal vaultHolder record.depositor
      record.asset record.amount hAuthorized hAllowed
    registry := escrowRegistryExpire before.registry id record }

/--
Expiry is a permissioned timeout-refund transition. It is available at or
after the deadline and returns the still-pending escrow to its depositor,
marking the record `expired` rather than voluntarily `cancelled`. A dedicated
expiry permission and ordinary transfer permission are required.
-/
def EscrowTimeLockedExpireStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (record : EscrowRecord Holder Asset) (principal : Principal),
    before.escrow.registry.records id = some record ∧
    record.phase = EscrowPhase.pending ∧
    expiresAt id ≤ before.currentTime ∧
    ∃ (hTransfer : policy.mayTransfer before.escrow.financial.holdings principal
        vaultHolder record.depositor record.asset record.amount)
      (_hEscrow : escrowPolicy.mayExpireEscrow before.escrow.financial.holdings
        principal vaultHolder record.depositor record.beneficiary record.asset
        record.amount)
      (hAllowed : TransferAllowed before.escrow.financial.holdings
        vaultHolder record.depositor record.asset record.amount),
      after =
        { escrow := escrowFinancialRegistryExpire policy mapping vaultHolder
            before.escrow id record principal hTransfer hAllowed
          currentTime := before.currentTime }

/-- Time advances strictly and cannot mutate financial or registry state. -/
def EscrowTimeAdvanceStep
    {EscrowId Holder LedgerAccount Asset : Type}
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ nextTime, before.currentTime < nextTime ∧
    after = { before with currentTime := nextTime }

/-- The only timed escrow transitions: open, pre-deadline release/cancel,
    post-deadline expiry refund, and monotone time advance. -/
def EscrowTimeLockedFinancialRegistryStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset) : Prop :=
  (∃ id, EscrowTimeLockedOpenStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowTimeLockedReleaseStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowTimeLockedCancelStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  (∃ id, EscrowTimeLockedExpireStep policy escrowPolicy mapping vaultHolder
    expiresAt id before after) ∨
  EscrowTimeAdvanceStep before after

/-- Expiry preserves conservation, the pending reserve, and the mapped vault GL. -/
theorem escrowFinancialRegistryExpire_preserves_invariant
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    {before : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset}
    (hBefore : EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder before)
    (id : EscrowId) (record : EscrowRecord Holder Asset) (principal : Principal)
    (hRecord : before.registry.records id = some record)
    (hPending : record.phase = EscrowPhase.pending)
    (hTransfer : policy.mayTransfer before.financial.holdings principal
      vaultHolder record.depositor record.asset record.amount)
    (_hEscrow : escrowPolicy.mayExpireEscrow before.financial.holdings principal
      vaultHolder record.depositor record.beneficiary record.asset record.amount)
    (hAllowed : TransferAllowed before.financial.holdings vaultHolder
      record.depositor record.asset record.amount) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
      (escrowFinancialRegistryExpire policy mapping vaultHolder before id record
        principal hTransfer hAllowed) := by
  have hVaultRoles := hBefore.pending_records_exclude_vault id record hRecord hPending
  have hFinancial :=
    escrowFinancialRegistryTransferFinancial_preserves_conservation
      policy mapping openingLedger before.financial hBefore.financial_conservation
      principal vaultHolder record.depositor record.asset record.amount
      hTransfer hAllowed
  have hRegistry := escrowRegistryExpire_preserves_invariant
    before.registry id record hBefore.registry_valid hRecord hPending
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [escrowFinancialRegistryExpire] using hFinancial
  · simpa [escrowFinancialRegistryExpire] using hRegistry
  · intro queryAsset
    have hBalance := escrowFinancialRegistryTransfer_source_balance
      policy mapping before.financial principal vaultHolder record.depositor
      record.asset queryAsset record.amount hTransfer hAllowed hVaultRoles.1
    calc
      (escrowFinancialRegistryExpire policy mapping vaultHolder before id record
        principal hTransfer hAllowed).financial.holdings.balance vaultHolder queryAsset =
        before.financial.holdings.balance vaultHolder queryAsset -
          (if queryAsset = record.asset then (record.amount : Int) else 0) := by
            simpa [escrowFinancialRegistryExpire] using hBalance
      _ = pooledEscrowReserve before.registry queryAsset -
          (if record.asset = queryAsset then (record.amount : Int) else 0) := by
            rw [hBefore.vault_matches_pending queryAsset]
            simp [eq_comm]
      _ = pooledEscrowReserve (escrowRegistryExpire before.registry id record) queryAsset := by
            symm
            exact pooledEscrowReserve_expire before.registry id record queryAsset
              hRecord hPending
  · intro query found hFound hPendingAfter
    by_cases hQuery : query = id
    · subst query
      have hFound' : some { record with phase := EscrowPhase.expired } = some found := by
        simpa [escrowFinancialRegistryExpire, escrowRegistryExpire] using hFound
      have hRecordEq : { record with phase := EscrowPhase.expired } = found :=
        Option.some.inj hFound'
      subst found
      cases hPendingAfter
    · have hOld : before.registry.records query = some found := by
        simpa [escrowFinancialRegistryExpire, escrowRegistryExpire, hQuery] using hFound
      exact hBefore.pending_records_exclude_vault query found hOld hPendingAfter

/-- Every time-locked escrow transition preserves the integrated financial invariant. -/
theorem escrowTimeLockedFinancialRegistryStep_preserves_invariant
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    {before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset}
    (hBefore : EscrowTimeLockedFinancialRegistryInvariant
      mapping openingLedger vaultHolder before)
    (hStep : EscrowTimeLockedFinancialRegistryStep policy escrowPolicy
      mapping vaultHolder expiresAt before after) :
    EscrowTimeLockedFinancialRegistryInvariant
      mapping openingLedger vaultHolder after := by
  change EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
    before.escrow at hBefore
  change EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
    after.escrow
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨id, hOpen⟩
    rcases hOpen with
      ⟨principal, depositor, beneficiary, asset, amount,
        hFresh, _hBeforeDeadline, hVaultDepositor, hVaultBeneficiary,
        hPositive, hTransfer, hEscrow, hAllowed, hAfter⟩
    subst after
    exact escrowFinancialRegistryOpen_preserves_invariant
      policy escrowPolicy mapping openingLedger vaultHolder hBefore id principal
      depositor beneficiary asset amount hFresh hVaultDepositor hVaultBeneficiary
      hPositive hTransfer hEscrow hAllowed
  · rcases hRest with hRelease | hRest
    · rcases hRelease with ⟨id, hRelease⟩
      rcases hRelease with
        ⟨record, principal, hRecord, hPending, _hBeforeDeadline,
          hTransfer, hEscrow, hAllowed, hAfter⟩
      subst after
      exact escrowFinancialRegistryRelease_preserves_invariant
        policy escrowPolicy mapping openingLedger vaultHolder hBefore id record
        principal hRecord hPending hTransfer hEscrow hAllowed
    · rcases hRest with hCancel | hRest
      · rcases hCancel with ⟨id, hCancel⟩
        rcases hCancel with
          ⟨record, principal, hRecord, hPending, _hBeforeDeadline,
            hTransfer, hEscrow, hAllowed, hAfter⟩
        subst after
        exact escrowFinancialRegistryCancel_preserves_invariant
          policy escrowPolicy mapping openingLedger vaultHolder hBefore id record
          principal hRecord hPending hTransfer hEscrow hAllowed
      · rcases hRest with hExpire | hAdvance
        · rcases hExpire with ⟨id, hExpire⟩
          rcases hExpire with
            ⟨record, principal, hRecord, hPending, _hDeadlineReached,
              hTransfer, hEscrow, hAllowed, hAfter⟩
          subst after
          exact escrowFinancialRegistryExpire_preserves_invariant
            policy escrowPolicy mapping openingLedger vaultHolder hBefore id record
            principal hRecord hPending hTransfer hEscrow hAllowed
        · rcases hAdvance with ⟨nextTime, _hForward, rfl⟩
          exact hBefore

/-- Every admitted timed transition leaves the clock unchanged or advances it. -/
theorem escrowTimeLockedFinancialRegistryStep_time_monotone
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    {before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset}
    (hStep : EscrowTimeLockedFinancialRegistryStep policy escrowPolicy
      mapping vaultHolder expiresAt before after) :
    before.currentTime ≤ after.currentTime := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with ⟨id, hOpen⟩
    rcases hOpen with
      ⟨principal, depositor, beneficiary, asset, amount,
        _hFresh, _hBeforeDeadline, _hVaultDepositor, _hVaultBeneficiary,
        _hPositive, _hTransfer, _hEscrow, _hAllowed, hAfter⟩
    rw [hAfter]
  · rcases hRest with hRelease | hRest
    · rcases hRelease with ⟨id, hRelease⟩
      rcases hRelease with
        ⟨record, principal, _hRecord, _hPending, _hBeforeDeadline,
          _hTransfer, _hEscrow, _hAllowed, hAfter⟩
      rw [hAfter]
    · rcases hRest with hCancel | hRest
      · rcases hCancel with ⟨id, hCancel⟩
        rcases hCancel with
          ⟨record, principal, _hRecord, _hPending, _hBeforeDeadline,
            _hTransfer, _hEscrow, _hAllowed, hAfter⟩
        rw [hAfter]
      · rcases hRest with hExpire | hAdvance
        · rcases hExpire with ⟨id, hExpire⟩
          rcases hExpire with
            ⟨record, principal, _hRecord, _hPending, _hDeadlineReached,
              _hTransfer, _hEscrow, _hAllowed, hAfter⟩
          rw [hAfter]
        · rcases hAdvance with ⟨nextTime, hForward, hAfter⟩
          rw [hAfter]
          exact le_of_lt hForward

/-- A fresh escrow cannot be opened when its assigned deadline has elapsed. -/
theorem escrowTimeLockedOpenStep_rejects_expired
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hElapsed : expiresAt id ≤ before.currentTime) :
    ¬ EscrowTimeLockedOpenStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hOpen
  rcases hOpen with
    ⟨principal, depositor, beneficiary, asset, amount, _hFresh,
      hBeforeDeadline, _hVaultDepositor, _hVaultBeneficiary, _hPositive,
      _hTransfer, _hEscrow, _hAllowed, _hAfter⟩
  exact (not_lt_of_ge hElapsed) hBeforeDeadline

/-- A release step is impossible at or after the selected escrow's deadline. -/
theorem escrowTimeLockedReleaseStep_rejects_expired
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hElapsed : expiresAt id ≤ before.currentTime) :
    ¬ EscrowTimeLockedReleaseStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hRelease
  rcases hRelease with
    ⟨record, principal, _hRecord, _hPending, hBeforeDeadline,
      _hTransfer, _hEscrow, _hAllowed, _hAfter⟩
  exact (not_lt_of_ge hElapsed) hBeforeDeadline

/-- Voluntary cancellation is impossible at or after the selected deadline. -/
theorem escrowTimeLockedCancelStep_rejects_expired
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hElapsed : expiresAt id ≤ before.currentTime) :
    ¬ EscrowTimeLockedCancelStep policy escrowPolicy mapping vaultHolder
      expiresAt id before after := by
  intro hCancel
  rcases hCancel with
    ⟨record, principal, _hRecord, _hPending, hBeforeDeadline,
      _hTransfer, _hEscrow, _hAllowed, _hAfter⟩
  exact (not_lt_of_ge hElapsed) hBeforeDeadline

/-- An expiry step cannot be invoked before its selected deadline. -/
theorem escrowTimeLockedExpireStep_requires_elapsed_deadline
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (id : EscrowId)
    (before after : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hExpire : EscrowTimeLockedExpireStep policy escrowPolicy mapping
      vaultHolder expiresAt id before after) :
    expiresAt id ≤ before.currentTime := by
  rcases hExpire with
    ⟨record, principal, _hRecord, _hPending, hElapsed,
      _hTransfer, _hEscrow, _hAllowed, _hAfter⟩
  exact hElapsed

/-- A verified machine for financially integrated escrow with fixed per-ID deadlines. -/
def escrowTimeLockedFinancialRegistryMachine
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (initialState : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowTimeLockedFinancialRegistryInvariant
      mapping openingLedger vaultHolder initialState) :
    VerifiedStateMachine
      (EscrowTimeLockedFinancialRegistryState
        EscrowId Holder LedgerAccount Asset) where
  invariant := EscrowTimeLockedFinancialRegistryInvariant mapping openingLedger vaultHolder
  initial := fun state => state = initialState
  step := EscrowTimeLockedFinancialRegistryStep policy escrowPolicy mapping
    vaultHolder expiresAt
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact escrowTimeLockedFinancialRegistryStep_preserves_invariant
      policy escrowPolicy mapping openingLedger vaultHolder expiresAt hBefore hStep

/-- Every reachable time-locked state retains exact pooled and mapped-GL backing. -/
theorem escrowTimeLockedFinancialRegistryInvariant_of_reachable
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (expiresAt : EscrowId → Nat)
    (initialState : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowTimeLockedFinancialRegistryInvariant
      mapping openingLedger vaultHolder initialState)
    {state : EscrowTimeLockedFinancialRegistryState
      EscrowId Holder LedgerAccount Asset}
    (hReachable : Reachable
      (escrowTimeLockedFinancialRegistryMachine policy escrowPolicy mapping
        openingLedger vaultHolder expiresAt initialState hInitial) state) :
    EscrowTimeLockedFinancialRegistryInvariant mapping openingLedger vaultHolder state :=
  invariant_of_reachable
    (escrowTimeLockedFinancialRegistryMachine policy escrowPolicy mapping
      openingLedger vaultHolder expiresAt initialState hInitial) hReachable

end SIRM
