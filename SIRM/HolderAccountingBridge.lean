import SIRM.Accounting
import SIRM.Holdings

/-!
# Holder / General-Ledger Subledger Bridge

This module relates the holder-balance projection to designated subledger
accounts in the signed general ledger. It does not identify the full general
ledger with the holder universe: unmapped control, liability, asset, equity,
income, and expense accounts remain ordinary ledger accounts.
-/

namespace SIRM

/--
An injective assignment of each holder to its designated general-ledger
subledger account. Injectivity prevents two distinct holders from sharing
one designated subledger account.
-/
structure HolderLedgerMap (Holder LedgerAccount : Type) where
  ledgerAccount : Holder → LedgerAccount
  injective_ledgerAccount : Function.Injective ledgerAccount

/--
The designated subledger account for each holder records the same signed
coordinate as the holder-balance projection. This is a relation between
selected subledger accounts, not an assertion that every general-ledger
account is a holder account.
-/
def HolderSubledgerAgreement
    {Holder LedgerAccount Asset : Type}
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (holdings : HoldingsState Holder Asset)
    (ledger : Ledger LedgerAccount Asset) : Prop :=
  ∀ holder asset,
    ledger.balance (mapping.ledgerAccount holder) asset =
      holdings.balance holder asset

/-- A holder transfer uses the matching balanced journal on mapped subledgers. -/
def holderTransferJournal
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (source destination : Holder) (asset : Asset) (amount : Nat) :
    JournalEntry LedgerAccount Asset :=
  transferJournal
    (mapping.ledgerAccount source)
    (mapping.ledgerAccount destination)
    asset amount

/--
At a mapped account, the journal posting is exactly the holder-side debit
and credit. Injectivity of the mapping is essential for this identity.
-/
theorem holderTransferJournal_posting
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (source destination holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (holderTransferJournal mapping source destination asset amount).posting
        (mapping.ledgerAccount holder) currentAsset =
      if currentAsset = asset then
        (if holder = source then -(amount : Int) else 0) +
        (if holder = destination then (amount : Int) else 0)
      else 0 := by
  classical
  have hSource :
      mapping.ledgerAccount holder = mapping.ledgerAccount source ↔
        holder = source := by
    constructor
    · intro h
      exact mapping.injective_ledgerAccount h
    · intro h
      cases h
      rfl
  have hDestination :
      mapping.ledgerAccount holder = mapping.ledgerAccount destination ↔
        holder = destination := by
    constructor
    · intro h
      exact mapping.injective_ledgerAccount h
    · intro h
      cases h
      rfl
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp [holderTransferJournal, transferJournal, hSource, hDestination]
  · simp [holderTransferJournal, transferJournal, hAsset]

/-- Pointwise effect of posting the holder-transfer journal to the ledger. -/
theorem postJournal_holderTransfer_balance
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    [DecidableEq Holder]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (ledger : Ledger LedgerAccount Asset)
    (source destination holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (postJournal ledger
      (holderTransferJournal mapping source destination asset amount)).balance
        (mapping.ledgerAccount holder) currentAsset =
      ledger.balance (mapping.ledgerAccount holder) currentAsset +
        (if currentAsset = asset then
          (if holder = source then -(amount : Int) else 0) +
          (if holder = destination then (amount : Int) else 0)
        else 0) := by
  simp [postJournal, holderTransferJournal_posting]

/--
A funded holder transfer and its matching balanced journal preserve the
pointwise subledger agreement. The theorem concerns only mapped accounts;
additional general-ledger accounts are not silently treated as holders.
-/
theorem holderSubledgerAgreement_transfer
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (holdings : HoldingsState Holder Asset)
    (ledger : Ledger LedgerAccount Asset)
    (hAgreement : HolderSubledgerAgreement mapping holdings ledger)
    (source destination : Holder) (asset : Asset) (amount : Nat)
    (_hAllowed : TransferAllowed holdings source destination asset amount) :
    HolderSubledgerAgreement mapping
      (executeTransfer holdings source destination asset amount _hAllowed)
      (postJournal ledger
        (holderTransferJournal mapping source destination asset amount)) := by
  intro holder currentAsset
  rw [postJournal_holderTransfer_balance, hAgreement holder currentAsset]
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp only [executeTransfer, transferBetweenHolders]
    by_cases hSourceHolder : holder = source
    · subst holder
      simp
      ring
    · by_cases hDestinationHolder : holder = destination
      · have hDestinationNeSource : destination ≠ source := by
          intro hEqual
          exact hSourceHolder (hDestinationHolder.trans hEqual)
        subst holder
        simp [hDestinationNeSource]
      · simp [hSourceHolder, hDestinationHolder]
  · simp [executeTransfer, transferBetweenHolders, hAsset]

/-- The mapped transfer journal is balanced for each asset. -/
theorem holderTransferJournal_balanced
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (source destination : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (∑ account : LedgerAccount,
      (holderTransferJournal mapping source destination asset amount).posting
        account currentAsset) = 0 :=
  (holderTransferJournal mapping source destination asset amount).balanced currentAsset

/-- Posting the mapped transfer journal preserves aggregate signed GL balance. -/
theorem holderTransferJournal_preserves_totalSignedBalance
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (ledger : Ledger LedgerAccount Asset)
    (source destination : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    totalSignedBalance
      (postJournal ledger
        (holderTransferJournal mapping source destination asset amount))
      currentAsset =
    totalSignedBalance ledger currentAsset :=
  totalSignedBalance_postJournal ledger
    (holderTransferJournal mapping source destination asset amount)
    currentAsset


/-!
## Issuance and burn journal bridges

Issuance and burn require a balancing general-ledger counterpart account
outside the holder-subledger mapping. Its accounting classification is
intentionally left open; these definitions specify only the balanced
double-entry mechanics.
-/

/--
Issue units to a holder's designated subledger by crediting that subledger
and debiting a designated non-holder counterpart account.
-/
def holderIssuanceJournal
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (recipient : Holder) (asset : Asset) (amount : Nat) :
    JournalEntry LedgerAccount Asset :=
  transferJournal counterpart (mapping.ledgerAccount recipient) asset amount

/-- A holder issuance journal is balanced independently for every asset. -/
theorem holderIssuanceJournal_balanced
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (recipient : Holder) (asset currentAsset : Asset) (amount : Nat) :
    (∑ account : LedgerAccount,
      (holderIssuanceJournal mapping counterpart recipient asset amount).posting
        account currentAsset) = 0 :=
  (holderIssuanceJournal mapping counterpart recipient asset amount).balanced
    currentAsset

/--
At any mapped holder account, an issuance journal posts exactly the matching
holder credit. The unmapped counterpart cannot alter a holder subledger.
-/
theorem holderIssuanceJournal_posting
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (recipient holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (holderIssuanceJournal mapping counterpart recipient asset amount).posting
        (mapping.ledgerAccount holder) currentAsset =
      if currentAsset = asset then
        (if holder = recipient then (amount : Int) else 0)
      else 0 := by
  classical
  have hMapped :
      mapping.ledgerAccount holder = mapping.ledgerAccount recipient ↔
        holder = recipient := by
    constructor
    · intro h
      exact mapping.injective_ledgerAccount h
    · intro h
      cases h
      rfl
  have hNotCounterpart :
      mapping.ledgerAccount holder ≠ counterpart :=
    Ne.symm (hCounterpart holder)
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp [holderIssuanceJournal, transferJournal, hMapped, hNotCounterpart]
  · simp [holderIssuanceJournal, transferJournal, hAsset]

/-- Pointwise ledger effect of a holder issuance at a mapped subledger. -/
theorem postJournal_holderIssuance_balance
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (ledger : Ledger LedgerAccount Asset)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (recipient holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (postJournal ledger
      (holderIssuanceJournal mapping counterpart recipient asset amount)).balance
        (mapping.ledgerAccount holder) currentAsset =
      ledger.balance (mapping.ledgerAccount holder) currentAsset +
        (if currentAsset = asset then
          (if holder = recipient then (amount : Int) else 0)
        else 0) := by
  change ledger.balance (mapping.ledgerAccount holder) currentAsset +
    (holderIssuanceJournal mapping counterpart recipient asset amount).posting
      (mapping.ledgerAccount holder) currentAsset = _
  rw [holderIssuanceJournal_posting mapping counterpart hCounterpart
    recipient holder asset currentAsset amount]

/--
A holder issuance and its matching journal preserve the pointwise agreement
between holder balances and designated general-ledger subaccounts.
-/
theorem holderSubledgerAgreement_issue
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (holdings : HoldingsState Holder Asset)
    (ledger : Ledger LedgerAccount Asset)
    (hAgreement : HolderSubledgerAgreement mapping holdings ledger)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (recipient : Holder) (asset : Asset) (amount : Nat) :
    HolderSubledgerAgreement mapping
      (issueToHolder holdings recipient asset amount)
      (postJournal ledger
        (holderIssuanceJournal mapping counterpart recipient asset amount)) := by
  intro holder currentAsset
  rw [postJournal_holderIssuance_balance mapping ledger counterpart
    hCounterpart recipient holder asset currentAsset amount]
  rw [hAgreement holder currentAsset]
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp [issueToHolder]
  · simp [issueToHolder, hAsset]

/--
Burn units from a holder's designated subledger by debiting that subledger
and crediting the designated unmapped counterpart account.
-/
def holderBurnJournal
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (holder : Holder) (asset : Asset) (amount : Nat) :
    JournalEntry LedgerAccount Asset :=
  transferJournal (mapping.ledgerAccount holder) counterpart asset amount

/-- A holder burn journal is balanced independently for every asset. -/
theorem holderBurnJournal_balanced
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (holder : Holder) (asset currentAsset : Asset) (amount : Nat) :
    (∑ account : LedgerAccount,
      (holderBurnJournal mapping counterpart holder asset amount).posting
        account currentAsset) = 0 :=
  (holderBurnJournal mapping counterpart holder asset amount).balanced
    currentAsset

/--
At any mapped holder account, a burn journal posts exactly the matching
holder debit. The unmapped counterpart cannot alter a holder subledger.
-/
theorem holderBurnJournal_posting
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (burnedHolder holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (holderBurnJournal mapping counterpart burnedHolder asset amount).posting
        (mapping.ledgerAccount holder) currentAsset =
      if currentAsset = asset then
        (if holder = burnedHolder then -(amount : Int) else 0)
      else 0 := by
  classical
  have hMapped :
      mapping.ledgerAccount holder = mapping.ledgerAccount burnedHolder ↔
        holder = burnedHolder := by
    constructor
    · intro h
      exact mapping.injective_ledgerAccount h
    · intro h
      cases h
      rfl
  have hNotCounterpart :
      mapping.ledgerAccount holder ≠ counterpart :=
    Ne.symm (hCounterpart holder)
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp [holderBurnJournal, transferJournal, hMapped, hNotCounterpart]
  · simp [holderBurnJournal, transferJournal, hAsset]

/-- Pointwise ledger effect of a holder burn at a mapped subledger. -/
theorem postJournal_holderBurn_balance
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [Fintype LedgerAccount]
    [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (ledger : Ledger LedgerAccount Asset)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (burnedHolder holder : Holder) (asset currentAsset : Asset)
    (amount : Nat) :
    (postJournal ledger
      (holderBurnJournal mapping counterpart burnedHolder asset amount)).balance
        (mapping.ledgerAccount holder) currentAsset =
      ledger.balance (mapping.ledgerAccount holder) currentAsset +
        (if currentAsset = asset then
          (if holder = burnedHolder then -(amount : Int) else 0)
        else 0) := by
  change ledger.balance (mapping.ledgerAccount holder) currentAsset +
    (holderBurnJournal mapping counterpart burnedHolder asset amount).posting
      (mapping.ledgerAccount holder) currentAsset = _
  rw [holderBurnJournal_posting mapping counterpart hCounterpart
    burnedHolder holder asset currentAsset amount]

/--
A holder burn and its matching journal preserve the pointwise agreement
between holder balances and designated general-ledger subaccounts.
-/
theorem holderSubledgerAgreement_burn
    {Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (holdings : HoldingsState Holder Asset)
    (ledger : Ledger LedgerAccount Asset)
    (hAgreement : HolderSubledgerAgreement mapping holdings ledger)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder, counterpart ≠ mapping.ledgerAccount holder)
    (holder : Holder) (asset : Asset) (amount : Nat) :
    HolderSubledgerAgreement mapping
      (burnFromHolder holdings holder asset amount)
      (postJournal ledger
        (holderBurnJournal mapping counterpart holder asset amount)) := by
  intro currentHolder currentAsset
  rw [postJournal_holderBurn_balance mapping ledger counterpart
    hCounterpart holder currentHolder asset currentAsset amount]
  rw [hAgreement currentHolder currentAsset]
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    by_cases hHolder : currentHolder = holder
    · simp [burnFromHolder, hHolder]; omega
    · simp [burnFromHolder, hHolder]
  · simp [burnFromHolder, hAsset]

end SIRM
