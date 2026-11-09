import SIRM.FinancialCore

/-! # SIRM Double-Entry Accounting Kernel

A journal entry is balanced when its signed postings sum to zero.
-/

namespace SIRM

variable (Account : Type) [Fintype Account] [DecidableEq Account]

def totalSignedBalance (balances : Account → Int) : Int :=
  ∑ account, balances account

structure JournalEntry where
  posting : Account → Int
  balanced : (∑ account, posting account) = 0

def post (balances : Account → Int) (entry : JournalEntry Account) :
    Account → Int :=
  fun account => balances account + entry.posting account

theorem totalSignedBalance_post
    (balances : Account → Int) (entry : JournalEntry Account) :
    totalSignedBalance Account (post Account balances entry) =
      totalSignedBalance Account balances := by
  classical
  simp [totalSignedBalance, post, Finset.sum_add_distrib, entry.balanced]

end SIRM
