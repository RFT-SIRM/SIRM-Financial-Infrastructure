import SIRM.FinancialCore

/-!
# SIRM Double-Entry Accounting

A journal entry is balanced separately for every asset. Values are signed
integer postings; this is distinct from the natural-number token supply book.
No conversion between different assets is implicit.
-/

namespace SIRM

/-- A ledger stores signed balances for each account and each asset. -/
structure Ledger (Account Asset : Type) where
  balance : Account → Asset → Int

/-- Aggregate signed balance for one asset across the finite account universe. -/
def totalSignedBalance {Account Asset : Type}
    [Fintype Account] [DecidableEq Account]
    (ledger : Ledger Account Asset) (asset : Asset) : Int :=
  ∑ account, ledger.balance account asset

/-- A journal entry carries signed postings and a balance proof per asset. -/
structure JournalEntry (Account Asset : Type)
    [Fintype Account] [DecidableEq Account] where
  posting : Account → Asset → Int
  balanced : ∀ asset, (∑ account : Account, posting account asset) = 0

/-- Applying a journal entry adds all of its postings atomically. -/
def postJournal {Account Asset : Type}
    [Fintype Account] [DecidableEq Account]
    (ledger : Ledger Account Asset) (entry : JournalEntry Account Asset) :
    Ledger Account Asset :=
  ⟨fun account asset => ledger.balance account asset + entry.posting account asset⟩

/-- A balanced journal preserves the aggregate signed balance of each asset. -/
theorem totalSignedBalance_postJournal {Account Asset : Type}
    [Fintype Account] [DecidableEq Account]
    (ledger : Ledger Account Asset) (entry : JournalEntry Account Asset)
    (asset : Asset) :
    totalSignedBalance (postJournal ledger entry) asset =
      totalSignedBalance ledger asset := by
  classical
  simp only [totalSignedBalance, postJournal, Finset.sum_add_distrib]
  rw [entry.balanced asset]
  simp

/--
A transfer is a balanced journal entry for one asset. The two postings cancel
when source and destination are distinct; if they are the same account, they
cancel within that account as well.
-/
def transferJournal {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (sourceAccount destinationAccount : Account)
    (asset : Asset) (amount : Nat) :
    JournalEntry Account Asset := by
  classical
  refine
    { posting := fun account currentAsset =>
        if currentAsset = asset then
          (if account = sourceAccount then -(amount : Int) else 0) +
          (if account = destinationAccount then (amount : Int) else 0)
        else 0
      balanced := ?_ }
  intro currentAsset
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    simp [Finset.sum_add_distrib]
  · simp [hAsset]

end SIRM
