import SIRM.EscrowPooledReserve

/-!
# Financially Integrated Multi-Record Escrow

This module closes the boundary left by `EscrowPooledReserve`: the pending
liability total is no longer paired with an independent abstract reserve
variable. It is identified directly with the balance of one designated
vault-holder inside `FinancialState`.

Every admitted open/release/cancel operation updates, in one abstract state
transition, (1) holder balances, (2) the matching mapped general-ledger
subledgers, and (3) the multi-ID escrow registry. The invariant proves that
the vault-holder balance equals the sum of pending escrow records for every
asset. Since `FinancialConservationInvariant` includes
`HolderSubledgerAgreement`, the mapped GL subledger for the vault-holder is
shown equal to that same pending total as well.

The model deliberately creates no second GL liability posting for the same
holder funds: the vault-holder remains one coordinate in the existing holder
partition, and the pool is a derived aggregate of registry records.
-/

namespace SIRM

/-- Joint state: the existing financial state and the multi-record registry. -/
structure EscrowFinancialRegistryState
    (EscrowId Holder LedgerAccount Asset : Type) where
  financial : FinancialState Holder LedgerAccount Asset
  registry : EscrowRegistry EscrowId Holder Asset

/--
A paired holder transfer and its existing balanced holder-subledger journal.
This is the only financial movement primitive used by this integration layer.
-/
def escrowFinancialRegistryTransferFinancial
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (before : FinancialState Holder LedgerAccount Asset)
    (principal : Principal) (source destination : Holder)
    (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer before.holdings principal source destination asset amount)
    (hAllowed : TransferAllowed before.holdings source destination asset amount) :
    FinancialState Holder LedgerAccount Asset :=
  { holdings := executeAuthorizedTransfer policy before.holdings principal
      source destination asset amount hAuthorized hAllowed
    ledger := postJournal before.ledger
      (holderTransferJournal mapping source destination asset amount) }

/--
The paired transfer preserves holder/supply reconciliation, mapped GL
agreement, and aggregate signed-GL conservation.
-/
theorem escrowFinancialRegistryTransferFinancial_preserves_conservation
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (before : FinancialState Holder LedgerAccount Asset)
    (hBefore : FinancialConservationInvariant mapping openingLedger before)
    (principal : Principal) (source destination : Holder)
    (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer before.holdings principal source destination asset amount)
    (hAllowed : TransferAllowed before.holdings source destination asset amount) :
    FinancialConservationInvariant mapping openingLedger
      (escrowFinancialRegistryTransferFinancial policy mapping before principal
        source destination asset amount hAuthorized hAllowed) := by
  simpa [escrowFinancialRegistryTransferFinancial] using
    (escrowTransferFinancial_preserves_conservation policy mapping openingLedger
      before hBefore principal source destination asset amount hAuthorized hAllowed)

/-- Exact credit at a transfer's destination, for each queried asset. -/
theorem escrowFinancialRegistryTransfer_destination_balance
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (before : FinancialState Holder LedgerAccount Asset)
    (principal : Principal) (source destination : Holder)
    (asset queryAsset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer before.holdings principal source destination asset amount)
    (hAllowed : TransferAllowed before.holdings source destination asset amount)
    (hDistinct : destination ≠ source) :
    (escrowFinancialRegistryTransferFinancial policy mapping before principal
      source destination asset amount hAuthorized hAllowed).holdings.balance
        destination queryAsset =
      before.holdings.balance destination queryAsset +
        (if queryAsset = asset then (amount : Int) else 0) := by
  by_cases hAsset : queryAsset = asset
  · subst queryAsset
    simp [escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
      executeTransfer, transferBetweenHolders, hDistinct]
  · simp [escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
      executeTransfer, transferBetweenHolders, hAsset]

/-- Exact debit at a transfer's source, for each queried asset. -/
theorem escrowFinancialRegistryTransfer_source_balance
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (before : FinancialState Holder LedgerAccount Asset)
    (principal : Principal) (source destination : Holder)
    (asset queryAsset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer before.holdings principal source destination asset amount)
    (hAllowed : TransferAllowed before.holdings source destination asset amount)
    (hDistinct : source ≠ destination) :
    (escrowFinancialRegistryTransferFinancial policy mapping before principal
      source destination asset amount hAuthorized hAllowed).holdings.balance
        source queryAsset =
      before.holdings.balance source queryAsset -
        (if queryAsset = asset then (amount : Int) else 0) := by
  by_cases hAsset : queryAsset = asset
  · subst queryAsset
    simp [escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
      executeTransfer, transferBetweenHolders, hDistinct]
  · simp [escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
      executeTransfer, transferBetweenHolders, hAsset]

/-- A newly opened pending record, before insertion into the registry. -/
def integratedPendingEscrowRecord
    {Holder Asset : Type}
    (depositor beneficiary : Holder) (asset : Asset) (amount : Nat) :
    EscrowRecord Holder Asset :=
  { depositor := depositor
    beneficiary := beneficiary
    asset := asset
    amount := amount
    phase := EscrowPhase.pending }

/-- Open one fresh escrow ID and transfer its funded amount into the vault-holder. -/
def escrowFinancialRegistryOpen
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (id : EscrowId) (principal : Principal)
    (depositor beneficiary : Holder) (asset : Asset) (amount : Nat)
    (hAuthorized :
      policy.mayTransfer before.financial.holdings principal
        depositor vaultHolder asset amount)
    (hAllowed :
      TransferAllowed before.financial.holdings depositor vaultHolder asset amount) :
    EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { financial := escrowFinancialRegistryTransferFinancial policy mapping
      before.financial principal depositor vaultHolder asset amount hAuthorized hAllowed
    registry := escrowRegistryInsert before.registry id
      (integratedPendingEscrowRecord depositor beneficiary asset amount) }

/-- Release one pending ID to its fixed beneficiary and mark that ID terminal. -/
def escrowFinancialRegistryRelease
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (principal : Principal)
    (hAuthorized :
      policy.mayTransfer before.financial.holdings principal
        vaultHolder record.beneficiary record.asset record.amount)
    (hAllowed :
      TransferAllowed before.financial.holdings vaultHolder
        record.beneficiary record.asset record.amount) :
    EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { financial := escrowFinancialRegistryTransferFinancial policy mapping
      before.financial principal vaultHolder record.beneficiary
      record.asset record.amount hAuthorized hAllowed
    registry := escrowRegistryRelease before.registry id record }

/-- Cancel one pending ID back to its depositor and mark that ID terminal. -/
def escrowFinancialRegistryCancel
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (id : EscrowId) (record : EscrowRecord Holder Asset)
    (principal : Principal)
    (hAuthorized :
      policy.mayTransfer before.financial.holdings principal
        vaultHolder record.depositor record.asset record.amount)
    (hAllowed :
      TransferAllowed before.financial.holdings vaultHolder
        record.depositor record.asset record.amount) :
    EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { financial := escrowFinancialRegistryTransferFinancial policy mapping
      before.financial principal vaultHolder record.depositor
      record.asset record.amount hAuthorized hAllowed
    registry := escrowRegistryCancel before.registry id record }

/-- Open requires a fresh ID, positive amount, separated vault roles, and both authorizations. -/
def EscrowFinancialRegistryOpenStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before after : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (id : EscrowId) (principal : Principal) (depositor beneficiary : Holder)
      (asset : Asset) (amount : Nat)
      (_hFresh : before.registry.records id = none)
      (_hVaultDepositor : vaultHolder ≠ depositor)
      (_hVaultBeneficiary : vaultHolder ≠ beneficiary)
      (_hPositive : 0 < amount)
      (hTransfer : policy.mayTransfer before.financial.holdings principal
        depositor vaultHolder asset amount)
      (_hEscrow : escrowPolicy.mayOpenEscrow before.financial.holdings principal
        depositor beneficiary vaultHolder asset amount)
      (hAllowed : TransferAllowed before.financial.holdings depositor vaultHolder asset amount),
    after = escrowFinancialRegistryOpen policy mapping vaultHolder before id principal
      depositor beneficiary asset amount hTransfer hAllowed

/-- Release requires the chosen ID to exist in pending phase and both authorizations. -/
def EscrowFinancialRegistryReleaseStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before after : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (id : EscrowId) (record : EscrowRecord Holder Asset) (principal : Principal)
      (_hRecord : before.registry.records id = some record)
      (_hPending : record.phase = EscrowPhase.pending)
      (hTransfer : policy.mayTransfer before.financial.holdings principal
        vaultHolder record.beneficiary record.asset record.amount)
      (_hEscrow : escrowPolicy.mayReleaseEscrow before.financial.holdings principal
        vaultHolder record.depositor record.beneficiary record.asset record.amount)
      (hAllowed : TransferAllowed before.financial.holdings vaultHolder
        record.beneficiary record.asset record.amount),
    after = escrowFinancialRegistryRelease policy mapping vaultHolder before id record
      principal hTransfer hAllowed

/-- Cancellation requires the chosen ID to exist in pending phase and both authorizations. -/
def EscrowFinancialRegistryCancelStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before after : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) : Prop :=
  ∃ (id : EscrowId) (record : EscrowRecord Holder Asset) (principal : Principal)
      (_hRecord : before.registry.records id = some record)
      (_hPending : record.phase = EscrowPhase.pending)
      (hTransfer : policy.mayTransfer before.financial.holdings principal
        vaultHolder record.depositor record.asset record.amount)
      (_hEscrow : escrowPolicy.mayCancelEscrow before.financial.holdings principal
        vaultHolder record.depositor record.beneficiary record.asset record.amount)
      (hAllowed : TransferAllowed before.financial.holdings vaultHolder
        record.depositor record.asset record.amount),
    after = escrowFinancialRegistryCancel policy mapping vaultHolder before id record
      principal hTransfer hAllowed

/-- The full integrated machine admits only authorized open/release/cancel transitions. -/
def EscrowFinancialRegistryStep
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (vaultHolder : Holder)
    (before after : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) : Prop :=
  EscrowFinancialRegistryOpenStep policy escrowPolicy mapping vaultHolder before after ∨
    EscrowFinancialRegistryReleaseStep policy escrowPolicy mapping vaultHolder before after ∨
    EscrowFinancialRegistryCancelStep policy escrowPolicy mapping vaultHolder before after

/--
The integrated invariant: the complete financial invariant, valid registry,
exact equality between actual vault-holder funds and pending records, and a
role-separation condition for every pending record.
-/
structure EscrowFinancialRegistryInvariant
    {EscrowId Holder LedgerAccount Asset : Type}
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (state : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) : Prop where
  financial_conservation :
    FinancialConservationInvariant mapping openingLedger state.financial
  registry_valid : EscrowRegistryInvariant state.registry
  vault_matches_pending :
    ∀ asset, state.financial.holdings.balance vaultHolder asset =
      pooledEscrowReserve state.registry asset
  pending_records_exclude_vault :
    ∀ id record, state.registry.records id = some record →
      record.phase = EscrowPhase.pending →
        vaultHolder ≠ record.depositor ∧ vaultHolder ≠ record.beneficiary

/-- Opening preserves the complete integrated invariant. -/
theorem escrowFinancialRegistryOpen_preserves_invariant
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
    (id : EscrowId) (principal : Principal) (depositor beneficiary : Holder)
    (asset : Asset) (amount : Nat)
    (hFresh : before.registry.records id = none)
    (hVaultDepositor : vaultHolder ≠ depositor)
    (hVaultBeneficiary : vaultHolder ≠ beneficiary)
    (hPositive : 0 < amount)
    (hTransfer : policy.mayTransfer before.financial.holdings principal
      depositor vaultHolder asset amount)
    (_hEscrow : escrowPolicy.mayOpenEscrow before.financial.holdings principal
      depositor beneficiary vaultHolder asset amount)
    (hAllowed : TransferAllowed before.financial.holdings depositor vaultHolder asset amount) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
      (escrowFinancialRegistryOpen policy mapping vaultHolder before id principal
        depositor beneficiary asset amount hTransfer hAllowed) := by
  let record := integratedPendingEscrowRecord depositor beneficiary asset amount
  have hFinancial :=
    escrowFinancialRegistryTransferFinancial_preserves_conservation
      policy mapping openingLedger before.financial hBefore.financial_conservation
      principal depositor vaultHolder asset amount hTransfer hAllowed
  have hRegistry := escrowRegistryInsert_preserves_invariant
    before.registry id record hBefore.registry_valid hFresh rfl hPositive
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [escrowFinancialRegistryOpen] using hFinancial
  · simpa [escrowFinancialRegistryOpen, record] using hRegistry
  · intro queryAsset
    have hBalance := escrowFinancialRegistryTransfer_destination_balance
      policy mapping before.financial principal depositor vaultHolder asset queryAsset
      amount hTransfer hAllowed hVaultDepositor
    calc
      (escrowFinancialRegistryOpen policy mapping vaultHolder before id principal
        depositor beneficiary asset amount hTransfer hAllowed).financial.holdings.balance
          vaultHolder queryAsset =
        before.financial.holdings.balance vaultHolder queryAsset +
          (if queryAsset = asset then (amount : Int) else 0) := by
            simpa [escrowFinancialRegistryOpen] using hBalance
      _ = pooledEscrowReserve before.registry queryAsset +
          (if record.asset = queryAsset then (record.amount : Int) else 0) := by
            rw [hBefore.vault_matches_pending queryAsset]
            by_cases hQueryAsset : queryAsset = asset
            · simp [record, integratedPendingEscrowRecord, hQueryAsset]
            · have hAssetQuery : asset ≠ queryAsset := fun h => hQueryAsset h.symm
              simp [record, integratedPendingEscrowRecord, hQueryAsset, hAssetQuery]
      _ = pooledEscrowReserve (escrowRegistryInsert before.registry id record) queryAsset := by
            symm
            exact pooledEscrowReserve_insert before.registry id record queryAsset hFresh rfl
  · intro query found hFound hPending
    by_cases hQuery : query = id
    · subst query
      have hFound' : some record = some found := by
        simpa [escrowFinancialRegistryOpen, escrowRegistryInsert, record] using hFound
      have hRecordEq : record = found := Option.some.inj hFound'
      subst found
      exact ⟨hVaultDepositor, hVaultBeneficiary⟩
    · have hOld : before.registry.records query = some found := by
        simpa [escrowFinancialRegistryOpen, escrowRegistryInsert, hQuery] using hFound
      exact hBefore.pending_records_exclude_vault query found hOld hPending

/-- Release preserves the complete integrated invariant. -/
theorem escrowFinancialRegistryRelease_preserves_invariant
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
      vaultHolder record.beneficiary record.asset record.amount)
    (_hEscrow : escrowPolicy.mayReleaseEscrow before.financial.holdings principal
      vaultHolder record.depositor record.beneficiary record.asset record.amount)
    (hAllowed : TransferAllowed before.financial.holdings vaultHolder
      record.beneficiary record.asset record.amount) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
      (escrowFinancialRegistryRelease policy mapping vaultHolder before id record
        principal hTransfer hAllowed) := by
  have hVaultRoles := hBefore.pending_records_exclude_vault id record hRecord hPending
  have hFinancial :=
    escrowFinancialRegistryTransferFinancial_preserves_conservation
      policy mapping openingLedger before.financial hBefore.financial_conservation
      principal vaultHolder record.beneficiary record.asset record.amount
      hTransfer hAllowed
  have hRegistry := escrowRegistryRelease_preserves_invariant
    before.registry id record hBefore.registry_valid hRecord hPending
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [escrowFinancialRegistryRelease] using hFinancial
  · simpa [escrowFinancialRegistryRelease] using hRegistry
  · intro queryAsset
    have hBalance := escrowFinancialRegistryTransfer_source_balance
      policy mapping before.financial principal vaultHolder record.beneficiary
      record.asset queryAsset record.amount hTransfer hAllowed hVaultRoles.2
    calc
      (escrowFinancialRegistryRelease policy mapping vaultHolder before id record
        principal hTransfer hAllowed).financial.holdings.balance vaultHolder queryAsset =
        before.financial.holdings.balance vaultHolder queryAsset -
          (if queryAsset = record.asset then (record.amount : Int) else 0) := by
            simpa [escrowFinancialRegistryRelease] using hBalance
      _ = pooledEscrowReserve before.registry queryAsset -
          (if record.asset = queryAsset then (record.amount : Int) else 0) := by
            rw [hBefore.vault_matches_pending queryAsset]
            simp [eq_comm]
      _ = pooledEscrowReserve (escrowRegistryRelease before.registry id record) queryAsset := by
            symm
            exact pooledEscrowReserve_release before.registry id record queryAsset
              hRecord hPending
  · intro query found hFound hPendingAfter
    by_cases hQuery : query = id
    · subst query
      have hFound' : some { record with phase := EscrowPhase.released } = some found := by
        simpa [escrowFinancialRegistryRelease, escrowRegistryRelease] using hFound
      have hRecordEq : { record with phase := EscrowPhase.released } = found :=
        Option.some.inj hFound'
      subst found
      cases hPendingAfter
    · have hOld : before.registry.records query = some found := by
        simpa [escrowFinancialRegistryRelease, escrowRegistryRelease, hQuery] using hFound
      exact hBefore.pending_records_exclude_vault query found hOld hPendingAfter

/-- Cancellation preserves the complete integrated invariant. -/
theorem escrowFinancialRegistryCancel_preserves_invariant
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
    (_hEscrow : escrowPolicy.mayCancelEscrow before.financial.holdings principal
      vaultHolder record.depositor record.beneficiary record.asset record.amount)
    (hAllowed : TransferAllowed before.financial.holdings vaultHolder
      record.depositor record.asset record.amount) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
      (escrowFinancialRegistryCancel policy mapping vaultHolder before id record
        principal hTransfer hAllowed) := by
  have hVaultRoles := hBefore.pending_records_exclude_vault id record hRecord hPending
  have hFinancial :=
    escrowFinancialRegistryTransferFinancial_preserves_conservation
      policy mapping openingLedger before.financial hBefore.financial_conservation
      principal vaultHolder record.depositor record.asset record.amount
      hTransfer hAllowed
  have hRegistry := escrowRegistryCancel_preserves_invariant
    before.registry id record hBefore.registry_valid hRecord hPending
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [escrowFinancialRegistryCancel] using hFinancial
  · simpa [escrowFinancialRegistryCancel] using hRegistry
  · intro queryAsset
    have hBalance := escrowFinancialRegistryTransfer_source_balance
      policy mapping before.financial principal vaultHolder record.depositor
      record.asset queryAsset record.amount hTransfer hAllowed hVaultRoles.1
    calc
      (escrowFinancialRegistryCancel policy mapping vaultHolder before id record
        principal hTransfer hAllowed).financial.holdings.balance vaultHolder queryAsset =
        before.financial.holdings.balance vaultHolder queryAsset -
          (if queryAsset = record.asset then (record.amount : Int) else 0) := by
            simpa [escrowFinancialRegistryCancel] using hBalance
      _ = pooledEscrowReserve before.registry queryAsset -
          (if record.asset = queryAsset then (record.amount : Int) else 0) := by
            rw [hBefore.vault_matches_pending queryAsset]
            simp [eq_comm]
      _ = pooledEscrowReserve (escrowRegistryCancel before.registry id record) queryAsset := by
            symm
            exact pooledEscrowReserve_cancel before.registry id record queryAsset
              hRecord hPending
  · intro query found hFound hPendingAfter
    by_cases hQuery : query = id
    · subst query
      have hFound' : some { record with phase := EscrowPhase.cancelled } = some found := by
        simpa [escrowFinancialRegistryCancel, escrowRegistryCancel] using hFound
      have hRecordEq : { record with phase := EscrowPhase.cancelled } = found :=
        Option.some.inj hFound'
      subst found
      cases hPendingAfter
    · have hOld : before.registry.records query = some found := by
        simpa [escrowFinancialRegistryCancel, escrowRegistryCancel, hQuery] using hFound
      exact hBefore.pending_records_exclude_vault query found hOld hPendingAfter

/-- Every integrated operation preserves actual vault balance = pending liability = mapped GL subledger. -/
theorem escrowFinancialRegistryStep_preserves_invariant
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    {before after : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset}
    (hBefore : EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder before)
    (hStep : EscrowFinancialRegistryStep policy escrowPolicy mapping vaultHolder before after) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder after := by
  rcases hStep with hOpen | hRest
  · rcases hOpen with
      ⟨id, principal, depositor, beneficiary, asset, amount,
        hFresh, hVaultDepositor, hVaultBeneficiary, hPositive,
        hTransfer, hEscrow, hAllowed, hAfter⟩
    subst after
    exact escrowFinancialRegistryOpen_preserves_invariant
      policy escrowPolicy mapping openingLedger vaultHolder hBefore id principal
      depositor beneficiary asset amount hFresh hVaultDepositor hVaultBeneficiary
      hPositive hTransfer hEscrow hAllowed
  · rcases hRest with hRelease | hCancel
    · rcases hRelease with
        ⟨id, record, principal, hRecord, hPending,
          hTransfer, hEscrow, hAllowed, hAfter⟩
      subst after
      exact escrowFinancialRegistryRelease_preserves_invariant
        policy escrowPolicy mapping openingLedger vaultHolder hBefore id record
        principal hRecord hPending hTransfer hEscrow hAllowed
    · rcases hCancel with
        ⟨id, record, principal, hRecord, hPending,
          hTransfer, hEscrow, hAllowed, hAfter⟩
      subst after
      exact escrowFinancialRegistryCancel_preserves_invariant
        policy escrowPolicy mapping openingLedger vaultHolder hBefore id record
        principal hRecord hPending hTransfer hEscrow hAllowed

/-- A verified state machine for the financially integrated escrow registry. -/
def escrowFinancialRegistryMachine
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (initialState : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder initialState) :
    VerifiedStateMachine (EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset) where
  invariant := EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
  initial := fun state => state = initialState
  step := EscrowFinancialRegistryStep policy escrowPolicy mapping vaultHolder
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact escrowFinancialRegistryStep_preserves_invariant
      policy escrowPolicy mapping openingLedger vaultHolder hBefore hStep

/-- Every reachable joint financial/registry state remains exactly backed. -/
theorem escrowFinancialRegistryInvariant_of_reachable
    {Principal EscrowId Holder LedgerAccount Asset : Type}
    [DecidableEq EscrowId] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (escrowPolicy : EscrowAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (initialState : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (hInitial : EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder initialState)
    {state : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset}
    (hReachable :
      Reachable
        (escrowFinancialRegistryMachine policy escrowPolicy mapping openingLedger
          vaultHolder initialState hInitial) state) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder state :=
  invariant_of_reachable
    (escrowFinancialRegistryMachine policy escrowPolicy mapping openingLedger
      vaultHolder initialState hInitial) hReachable

/-- Empty registry is integrated exactly when the initial vault-holder is empty. -/
def emptyEscrowFinancialRegistryState
    {EscrowId Holder LedgerAccount Asset : Type}
    (financial : FinancialState Holder LedgerAccount Asset) :
    EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset :=
  { financial := financial
    registry := emptyEscrowRegistry }

theorem emptyEscrowFinancialRegistryInvariant_of_zero_vault
    {EscrowId Holder LedgerAccount Asset : Type}
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (financial : FinancialState Holder LedgerAccount Asset)
    (hFinancial : FinancialConservationInvariant mapping openingLedger financial)
    (hVaultZero : ∀ asset, financial.holdings.balance vaultHolder asset = 0) :
    EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder
      (emptyEscrowFinancialRegistryState (EscrowId := EscrowId) financial) := by
  refine ⟨hFinancial, ?_, ?_, ?_⟩
  · intro id record hRecord
    simp [emptyEscrowFinancialRegistryState, emptyEscrowRegistry] at hRecord
  · intro asset
    change financial.holdings.balance vaultHolder asset =
      pooledEscrowReserve
        (emptyEscrowRegistry : EscrowRegistry EscrowId Holder Asset) asset
    rw [hVaultZero asset]
    simp [pooledEscrowReserve, pooledEscrowContribution, emptyEscrowRegistry]
  · intro id record hRecord hPending
    simp [emptyEscrowFinancialRegistryState, emptyEscrowRegistry] at hRecord

/-- The mapped vault GL subledger and actual vault holding are both the pending total. -/
theorem escrowFinancialRegistryVault_gl_equals_pending
    {EscrowId Holder LedgerAccount Asset : Type}
    [Fintype EscrowId] [Fintype Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (vaultHolder : Holder)
    (state : EscrowFinancialRegistryState EscrowId Holder LedgerAccount Asset)
    (hInvariant : EscrowFinancialRegistryInvariant mapping openingLedger vaultHolder state)
    (asset : Asset) :
    state.financial.holdings.balance vaultHolder asset =
        state.financial.ledger.balance (mapping.ledgerAccount vaultHolder) asset ∧
      state.financial.ledger.balance (mapping.ledgerAccount vaultHolder) asset =
        pooledEscrowReserve state.registry asset := by
  have hMapped := hInvariant.financial_conservation.1.2 vaultHolder asset
  constructor
  · exact hMapped.symm
  · calc
      state.financial.ledger.balance (mapping.ledgerAccount vaultHolder) asset =
          state.financial.holdings.balance vaultHolder asset := hMapped
      _ = pooledEscrowReserve state.registry asset := hInvariant.vault_matches_pending asset

end SIRM
