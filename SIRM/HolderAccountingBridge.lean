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
    simp [executeTransfer, transferBetweenHolders]
    ring
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

end SIRM
