import SIRM.FinancialCore

/-!
# SIRM Per-Asset Holdings and Supply Reconciliation

This module models the owner-balance view of issued assets. It is deliberately
separate from the signed general-ledger postings in `SIRM.Accounting`.

The account universe supplied to this model must include every account that
holds units of the asset exactly once, including protocol-controlled pools.
It must not include duplicated general-ledger liability or control entries.
-/

namespace SIRM

/-- Owner holdings and the per-asset issuance book. -/
structure HoldingsState (Account Asset : Type) where
  balance : Account → Asset → Int
  supply : Asset → SupplyState

/-- Total owner-held units of one asset, measured in its integer base unit. -/
def totalHoldings {Account Asset : Type} [Fintype Account]
    (state : HoldingsState Account Asset) (asset : Asset) : Int :=
  ∑ account : Account, state.balance account asset

/--
A holdings state is reconciled when:
* the supply book satisfies minted = burned + outstanding;
* every holder balance is nonnegative; and
* every outstanding unit appears in exactly one holder account.
-/
def HoldingsInvariant {Account Asset : Type} [Fintype Account]
    (state : HoldingsState Account Asset) : Prop :=
  ∀ asset,
    SupplyInvariant (state.supply asset) ∧
    (∀ account, 0 ≤ state.balance account asset) ∧
    totalHoldings state asset = (state.supply asset).outstanding

/-- Empty owner balances and zero supply form a valid starting state. -/
def emptyHoldingsState (Account Asset : Type) : HoldingsState Account Asset :=
  { balance := fun _ _ => 0
    supply := fun _ => initialSupply }

theorem emptyHoldingsState_invariant {Account Asset : Type} [Fintype Account] :
    HoldingsInvariant (emptyHoldingsState Account Asset) := by
  intro asset
  refine ⟨initialSupply_invariant, ?_, ?_⟩
  · intro account
    simp [emptyHoldingsState]
  · simp [totalHoldings, emptyHoldingsState, initialSupply]

/--
Any one holder's nonnegative balance is bounded by the total holdings.
This fact is later used to show that a holder cannot burn more than the
asset's total outstanding supply.
-/
theorem holderBalance_le_totalHoldings {Account Asset : Type}
    [Fintype Account] [DecidableEq Account]
    (state : HoldingsState Account Asset) (asset : Asset)
    (hNonnegative : ∀ account, 0 ≤ state.balance account asset)
    (holder : Account) :
    state.balance holder asset ≤ totalHoldings state asset := by
  classical
  unfold totalHoldings
  exact Finset.single_le_sum
    (fun account hAccount => hNonnegative account)
    (Finset.mem_univ holder)

/-- A transfer may be a self-transfer (a no-op) or must be fully funded. -/
def TransferAllowed {Account Asset : Type}
    (state : HoldingsState Account Asset)
    (source destination : Account) (asset : Asset) (amount : Nat) : Prop :=
  source = destination ∨ (amount : Int) ≤ state.balance source asset

/--
Move units between two holder accounts. The supply book is unchanged.
A self-transfer is defined by the same debit and credit and therefore leaves
the holder balance unchanged.
-/
def transferBetweenHolders {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (source destination : Account) (asset : Asset) (amount : Nat) :
    HoldingsState Account Asset :=
  { state with
    balance := fun account currentAsset =>
      if currentAsset = asset then
        state.balance account currentAsset +
          (if account = destination then (amount : Int) else 0) -
          (if account = source then (amount : Int) else 0)
      else state.balance account currentAsset }

/-- Transfers conserve the total units held for the transferred asset. -/
theorem totalHoldings_transferBetweenHolders {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (source destination : Account) (asset : Asset) (amount : Nat) :
    totalHoldings
      (transferBetweenHolders state source destination asset amount) asset =
      totalHoldings state asset := by
  classical
  simp [totalHoldings, transferBetweenHolders, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- A funded transfer preserves supply reconciliation and nonnegative balances. -/
theorem transferBetweenHolders_preserves_invariant {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (source destination : Account) (asset : Asset) (amount : Nat)
    (hAllowed : TransferAllowed state source destination asset amount) :
    HoldingsInvariant
      (transferBetweenHolders state source destination asset amount) := by
  intro currentAsset
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    rcases hInvariant asset with ⟨hSupply, hNonnegative, hTotal⟩
    refine ⟨hSupply, ?_, ?_⟩
    · intro account
      by_cases hSource : account = source
      · subst account
        by_cases hSelf : source = destination
        · simpa [transferBetweenHolders, hSelf] using hNonnegative source
        · have hFunds : (amount : Int) ≤ state.balance source asset := by
            rcases hAllowed with hEqual | hFunds
            · exact False.elim (hSelf hEqual)
            · exact hFunds
          simp [transferBetweenHolders, hSelf]
          omega
      · by_cases hDestination : account = destination
        · subst account
          have hDestinationNotSource : destination ≠ source := by
            intro hEqual
            exact hSource hEqual
          have hDestinationNonnegative : 0 ≤ state.balance destination asset :=
            hNonnegative destination
          simp [transferBetweenHolders, hDestinationNotSource]
          omega
        · simpa [transferBetweenHolders, hSource, hDestination] using
            hNonnegative account
    · rw [totalHoldings_transferBetweenHolders]
      exact hTotal
  · simpa [transferBetweenHolders, hAsset, totalHoldings] using
      hInvariant currentAsset


/--
Execute a transfer only when its arithmetic precondition is satisfied.
An invalid request produces no next state; a valid request produces
the corresponding holder-balance state.
This wrapper does not yet model signer or account-role authorization.
-/
def executeTransfer {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (source destination : Account) (asset : Asset) (amount : Nat) :
    Option (HoldingsState Account Asset) :=
  if TransferAllowed state source destination asset amount then
    some (transferBetweenHolders state source destination asset amount)
  else none

/-- Every successfully executed guarded transfer preserves the invariant. -/
theorem executeTransfer_preserves_invariant {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (source destination : Account) (asset : Asset) (amount : Nat) :
    ∀ next,
      executeTransfer state source destination asset amount = some next →
        HoldingsInvariant next := by
  intro next hNext
  by_cases hAllowed : TransferAllowed state source destination asset amount
  · have hEq : transferBetweenHolders state source destination asset amount = next := by
      simpa [executeTransfer, hAllowed] using hNext
    rw [← hEq]
    exact transferBetweenHolders_preserves_invariant state hInvariant
      source destination asset amount hAllowed
  · simp [executeTransfer, hAllowed] at hNext

/-- A transfer whose precondition fails is rejected without a next state. -/
theorem executeTransfer_rejects_unfunded {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (source destination : Account) (asset : Asset) (amount : Nat)
    (hNotAllowed : ¬ TransferAllowed state source destination asset amount) :
    executeTransfer state source destination asset amount = none := by
  simp [executeTransfer, hNotAllowed]

/--
Issue new units directly to one holder. Both the holder's balance and the
asset's supply book increase by the same amount.
-/
def issueToHolder {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (recipient : Account) (asset : Asset) (amount : Nat) :
    HoldingsState Account Asset :=
  { state with
    balance := fun account currentAsset =>
      if currentAsset = asset then
        state.balance account currentAsset +
          (if account = recipient then (amount : Int) else 0)
      else state.balance account currentAsset
    supply := fun currentAsset =>
      if currentAsset = asset then mint (state.supply currentAsset) amount
      else state.supply currentAsset }

/-- Issuance increases total holder balances by exactly the issued amount. -/
theorem totalHoldings_issueToHolder {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (recipient : Account) (asset : Asset) (amount : Nat) :
    totalHoldings (issueToHolder state recipient asset amount) asset =
      totalHoldings state asset + (amount : Int) := by
  classical
  simp [totalHoldings, issueToHolder, Finset.sum_add_distrib]

/-- Issuing to a holder preserves the per-asset supply reconciliation. -/
theorem issueToHolder_preserves_invariant {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (recipient : Account) (asset : Asset) (amount : Nat) :
    HoldingsInvariant (issueToHolder state recipient asset amount) := by
  intro currentAsset
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    rcases hInvariant asset with ⟨hSupply, hNonnegative, hTotal⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [issueToHolder] using
        (mint_preserves_invariant (state.supply asset) hSupply amount)
    · intro account
      by_cases hRecipient : account = recipient
      · have hRecipientNonnegative : 0 ≤ state.balance recipient asset :=
          hNonnegative recipient
        simp [issueToHolder, hRecipient]
        omega
      · simpa [issueToHolder, hRecipient] using hNonnegative account
    · rw [totalHoldings_issueToHolder, hTotal]
      simp [issueToHolder, mint]
  · simpa [issueToHolder, hAsset, totalHoldings] using
      hInvariant currentAsset

/--
Burn units from one holder. The amount is bounded by that holder's own
balance; the aggregate reconciliation proves this is also bounded by
outstanding supply.
-/
def burnFromHolder {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (holder : Account) (asset : Asset) (amount : Nat) :
    HoldingsState Account Asset :=
  { state with
    balance := fun account currentAsset =>
      if currentAsset = asset then
        state.balance account currentAsset -
          (if account = holder then (amount : Int) else 0)
      else state.balance account currentAsset
    supply := fun currentAsset =>
      if currentAsset = asset then burn (state.supply currentAsset) amount
      else state.supply currentAsset }

/-- Burning decreases total holder balances by exactly the burned amount. -/
theorem totalHoldings_burnFromHolder {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (holder : Account) (asset : Asset) (amount : Nat) :
    totalHoldings (burnFromHolder state holder asset amount) asset =
      totalHoldings state asset - (amount : Int) := by
  classical
  simp [totalHoldings, burnFromHolder, Finset.sum_sub_distrib]

/-- A holder-funded burn preserves supply reconciliation and nonnegative holdings. -/
theorem burnFromHolder_preserves_invariant {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (holder : Account) (asset : Asset) (amount : Nat)
    (hEnough : (amount : Int) ≤ state.balance holder asset) :
    HoldingsInvariant (burnFromHolder state holder asset amount) := by
  intro currentAsset
  by_cases hAsset : currentAsset = asset
  · subst currentAsset
    rcases hInvariant asset with ⟨hSupply, hNonnegative, hTotal⟩
    have hHolderLeTotal :
        state.balance holder asset ≤ totalHoldings state asset :=
      holderBalance_le_totalHoldings state asset hNonnegative holder
    have hAmountLeOutstandingInt :
        (amount : Int) ≤ (state.supply asset).outstanding := by
      calc
        (amount : Int) ≤ state.balance holder asset := hEnough
        _ ≤ totalHoldings state asset := hHolderLeTotal
        _ = (state.supply asset).outstanding := hTotal
    have hAmountLeOutstanding : amount ≤ (state.supply asset).outstanding := by
      exact_mod_cast hAmountLeOutstandingInt
    refine ⟨?_, ?_, ?_⟩
    · simpa [burnFromHolder] using
        (burn_preserves_invariant (state.supply asset) hSupply amount
          hAmountLeOutstanding)
    · intro account
      by_cases hHolder : account = holder
      · subst account
        simp [burnFromHolder]
        omega
      · simpa [burnFromHolder, hHolder] using hNonnegative account
    · rw [totalHoldings_burnFromHolder, hTotal]
      dsimp [burnFromHolder, burn]
      simp only [ite_true, Nat.cast_sub hAmountLeOutstanding]
  · simpa [burnFromHolder, hAsset, totalHoldings] using
      hInvariant currentAsset


/--
Execute a holder burn only when the holder owns enough units. An invalid
request returns no next state. Signer/role authorization remains a separate
protocol obligation.
-/
def executeBurn {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (holder : Account) (asset : Asset) (amount : Nat) :
    Option (HoldingsState Account Asset) :=
  if (amount : Int) ≤ state.balance holder asset then
    some (burnFromHolder state holder asset amount)
  else none

/-- Every successfully executed holder burn preserves the invariant. -/
theorem executeBurn_preserves_invariant {Account Asset : Type}
    [Fintype Account] [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (hInvariant : HoldingsInvariant state)
    (holder : Account) (asset : Asset) (amount : Nat) :
    ∀ next,
      executeBurn state holder asset amount = some next →
        HoldingsInvariant next := by
  intro next hNext
  by_cases hEnough : (amount : Int) ≤ state.balance holder asset
  · have hEq : burnFromHolder state holder asset amount = next := by
      simpa [executeBurn, hEnough] using hNext
    rw [← hEq]
    exact burnFromHolder_preserves_invariant state hInvariant
      holder asset amount hEnough
  · simp [executeBurn, hEnough] at hNext

/-- A holder burn exceeding its balance is rejected without a next state. -/
theorem executeBurn_rejects_excess {Account Asset : Type}
    [DecidableEq Account] [DecidableEq Asset]
    (state : HoldingsState Account Asset)
    (holder : Account) (asset : Asset) (amount : Nat)
    (hNotEnough : ¬ (amount : Int) ≤ state.balance holder asset) :
    executeBurn state holder asset amount = none := by
  simp [executeBurn, hNotEnough]

end SIRM
end SIRM
