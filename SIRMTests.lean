import SIRM

/-!
# SIRM theorem-level regression suite

These concrete scenarios exercise the public Lean transition theorems.
The suite is a Lake test-driver library: `lake test` must compile this file.
It is intentionally separate from the normative `SIRM` library.
-/

namespace SIRMTests

open SIRM

inductive DemoAccount
  | alice
  | bob
  | treasury
  deriving DecidableEq, Repr

/-- An explicit finite enumeration avoids relying on generated enum internals. -/
instance : Fintype DemoAccount :=
  Fintype.ofList [DemoAccount.alice, DemoAccount.bob, DemoAccount.treasury] (by
    intro account
    cases account <;> simp)

inductive DemoAsset
  | rft
  | usd
  deriving DecidableEq, Repr

/-- A two-asset state constructed only through the verified issuance transition. -/
def demoState : HoldingsState DemoAccount DemoAsset :=
  issueToHolder
    (issueToHolder
      (issueToHolder
        (issueToHolder
          (emptyHoldingsState DemoAccount DemoAsset)
          .alice .rft 100)
        .bob .rft 25)
      .treasury .rft 75)
    .alice .usd 1000

/-- Reconciliation follows compositionally from the verified issuance theorem. -/
theorem demoState_reconciled : HoldingsInvariant demoState := by
  unfold demoState
  apply issueToHolder_preserves_invariant
  apply issueToHolder_preserves_invariant
  apply issueToHolder_preserves_invariant
  apply issueToHolder_preserves_invariant
  exact emptyHoldingsState_invariant

/-- A funded RFT transfer moves 40 units from Alice to Bob. -/
def afterTransfer : HoldingsState DemoAccount DemoAsset :=
  transferBetweenHolders demoState .alice .bob .rft 40

theorem transfer40_is_funded :
    TransferAllowed demoState .alice .bob .rft 40 := by
  exact Or.inr (by decide)

theorem transfer40_preserves_reconciliation :
    HoldingsInvariant afterTransfer := by
  exact transferBetweenHolders_preserves_invariant demoState
    demoState_reconciled .alice .bob .rft 40 transfer40_is_funded

theorem transfer40_expected_balances :
    afterTransfer.balance .alice .rft = 60 ∧
    afterTransfer.balance .bob .rft = 65 ∧
    afterTransfer.balance .treasury .rft = 75 ∧
    afterTransfer.supply .rft = demoState.supply .rft := by
  decide

theorem transfer40_leaves_other_asset_unchanged :
    afterTransfer.balance .alice .usd = demoState.balance .alice .usd ∧
    afterTransfer.supply .usd = demoState.supply .usd := by
  decide

/-- Alice's RFT balance in the regression state is exactly 100 units. -/
theorem demoState_alice_rft_balance :
    demoState.balance DemoAccount.alice DemoAsset.rft = 100 := by
  simp [demoState, issueToHolder, emptyHoldingsState]

/-- Overspending is rejected by the transfer precondition. -/
theorem transfer101_is_not_funded :
    ¬ TransferAllowed demoState .alice .bob .rft 101 := by
  intro hAllowed
  change DemoAccount.alice = DemoAccount.bob ∨
    (101 : Int) ≤ demoState.balance DemoAccount.alice DemoAsset.rft at hAllowed
  rcases hAllowed with hSame | hFunds
  · cases hSame
  · rw [demoState_alice_rft_balance] at hFunds
    norm_num at hFunds


/-- The guarded command returns the exact state for a funded transfer. -/
theorem executeTransfer40_returns_expected :
    executeTransfer demoState .alice .bob .rft 40 = some afterTransfer := by
  simp [executeTransfer, transfer40_is_funded, afterTransfer]

/-- The guarded command produces no state for an over-funded transfer. -/
theorem executeTransfer101_is_rejected :
    executeTransfer demoState .alice .bob .rft 101 = none :=
  executeTransfer_rejects_unfunded demoState .alice .bob .rft 101
    transfer101_is_not_funded

/-- Every successful invocation in the concrete test state remains reconciled. -/
theorem executeTransfer40_preserves_reconciliation :
    ∀ next,
      executeTransfer demoState .alice .bob .rft 40 = some next →
        HoldingsInvariant next :=
  executeTransfer_preserves_invariant demoState demoState_reconciled
    .alice .bob .rft 40

/-- A self-transfer is permitted and leaves the account balances unchanged. -/
def afterSelfTransfer : HoldingsState DemoAccount DemoAsset :=
  transferBetweenHolders demoState .alice .alice .rft 999

theorem selfTransfer_is_allowed :
    TransferAllowed demoState .alice .alice .rft 999 := by
  exact Or.inl rfl

theorem selfTransfer_preserves_reconciliation :
    HoldingsInvariant afterSelfTransfer := by
  exact transferBetweenHolders_preserves_invariant demoState
    demoState_reconciled .alice .alice .rft 999 selfTransfer_is_allowed

theorem selfTransfer_is_a_noop :
    afterSelfTransfer.balance .alice .rft = demoState.balance .alice .rft ∧
    afterSelfTransfer.supply .rft = demoState.supply .rft := by
  decide

/-- Issuance credits the recipient and the outstanding supply equally. -/
def afterIssue : HoldingsState DemoAccount DemoAsset :=
  issueToHolder demoState .treasury .rft 15

theorem issue15_preserves_reconciliation :
    HoldingsInvariant afterIssue :=
  issueToHolder_preserves_invariant demoState demoState_reconciled
    .treasury .rft 15

theorem issue15_expected_state :
    afterIssue.balance .treasury .rft = 90 ∧
    afterIssue.supply .rft = ⟨215, 0, 215⟩ := by
  decide

/-- Burning is bounded by the selected holder's own balance. -/
def afterBurn : HoldingsState DemoAccount DemoAsset :=
  burnFromHolder demoState .alice .rft 20

theorem burn20_preserves_reconciliation :
    HoldingsInvariant afterBurn :=
  burnFromHolder_preserves_invariant demoState demoState_reconciled
    .alice .rft 20 (by decide)

theorem burn20_expected_state :
    afterBurn.balance .alice .rft = 80 ∧
    afterBurn.supply .rft = ⟨200, 20, 180⟩ := by
  decide


/-- The guarded command returns the exact state for a holder-funded burn. -/
theorem executeBurn20_returns_expected :
    executeBurn demoState .alice .rft 20 = some afterBurn := by
  have hEnough : (20 : Int) ≤ demoState.balance .alice .rft := by
    rw [demoState_alice_rft_balance]
    norm_num
  simp [executeBurn, hEnough, afterBurn]

/-- The guarded command rejects a burn larger than Alice's holdings. -/
theorem executeBurn101_is_rejected :
    executeBurn demoState .alice .rft 101 = none := by
  apply executeBurn_rejects_excess
  rw [demoState_alice_rft_balance]
  norm_num

/-- Every successful holder-burn invocation in the test state remains reconciled. -/
theorem executeBurn20_preserves_reconciliation :
    ∀ next,
      executeBurn demoState .alice .rft 20 = some next →
        HoldingsInvariant next :=
  executeBurn_preserves_invariant demoState demoState_reconciled
    .alice .rft 20

/-- The founder genesis allocation is an exact integer calculation. -/
theorem founderAllocation_example :
    founderAllocation 1_000_000_000_000 = 13_090_000_000 := by
  norm_num [founderAllocation, founderRatePpm, ppmScale]

theorem genesisPool_reconciles :
    GenesisAllocationInvariant (initialGenesisAllocation 1_000_000_000_000) :=
  initialGenesisAllocation_balanced _

/-- The balanced journal constructor is available for concrete finite types. -/
def demoLedger : Ledger DemoAccount DemoAsset :=
  ⟨fun _ _ => 0⟩

def demoJournal : JournalEntry DemoAccount DemoAsset :=
  transferJournal .alice .bob .rft 40

theorem journalTransfer_preserves_total :
    ∀ asset,
      totalSignedBalance (postJournal demoLedger demoJournal) asset =
        totalSignedBalance demoLedger asset := by
  intro asset
  exact totalSignedBalance_postJournal demoLedger demoJournal asset

end SIRMTests
