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



/-- A successful guarded transfer is the underlying proved transition. -/
theorem executeTransfer40_returns_expected :
    executeTransfer demoState .alice .bob .rft 40 transfer40_is_funded =
      afterTransfer := by
  rfl

/-- The proof-carrying transfer preserves reconciliation. -/
theorem executeTransfer40_preserves_reconciliation :
    HoldingsInvariant
      (executeTransfer demoState .alice .bob .rft 40 transfer40_is_funded) :=
  executeTransfer_preserves_invariant demoState demoState_reconciled
    .alice .bob .rft 40 transfer40_is_funded


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



/-- Alice has enough RFT for a 20-unit burn. -/
theorem alice_rft_can_burn_20 :
    (20 : Int) ≤ demoState.balance .alice .rft := by
  rw [demoState_alice_rft_balance]
  norm_num

/-- Alice does not have enough RFT for a 101-unit burn. -/
theorem alice_rft_cannot_burn_101 :
    ¬ (101 : Int) ≤ demoState.balance .alice .rft := by
  rw [demoState_alice_rft_balance]
  norm_num

/-- A successful guarded burn is the underlying proved transition. -/
theorem executeBurn20_returns_expected :
    executeBurn demoState .alice .rft 20 alice_rft_can_burn_20 =
      afterBurn := by
  rfl

/-- The proof-carrying burn preserves reconciliation. -/
theorem executeBurn20_preserves_reconciliation :
    HoldingsInvariant
      (executeBurn demoState .alice .rft 20 alice_rft_can_burn_20) :=
  executeBurn_preserves_invariant demoState demoState_reconciled
    .alice .rft 20 alice_rft_can_burn_20


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


inductive DemoLedgerAccount
  | aliceSubledger
  | bobSubledger
  | treasurySubledger
  | control
  deriving DecidableEq, Repr

/-- An unmapped control account remains outside the holder projection. -/
instance : Fintype DemoLedgerAccount :=
  Fintype.ofList
    [.aliceSubledger, .bobSubledger, .treasurySubledger, .control] (by
      intro account
      cases account <;> simp)

def demoHolderLedgerMap : HolderLedgerMap DemoAccount DemoLedgerAccount where
  ledgerAccount
    | .alice => .aliceSubledger
    | .bob => .bobSubledger
    | .treasury => .treasurySubledger
  injective_ledgerAccount := by
    intro left right h
    cases left <;> cases right <;> simp_all

def demoBridgeLedger : Ledger DemoLedgerAccount DemoAsset :=
  ⟨fun account asset =>
    match account, asset with
    | .aliceSubledger, .rft => 100
    | .bobSubledger, .rft => 25
    | .treasurySubledger, .rft => 75
    | .aliceSubledger, .usd => 1000
    | .bobSubledger, .usd => 0
    | .treasurySubledger, .usd => 0
    | .control, _ => 0⟩

theorem demoHolderSubledgerAgreement :
    HolderSubledgerAgreement demoHolderLedgerMap demoState demoBridgeLedger := by
  intro holder asset
  cases holder <;> cases asset <;>
    simp [demoHolderLedgerMap, demoBridgeLedger, demoState,
      issueToHolder, emptyHoldingsState]

def demoBridgeAfterHoldings : HoldingsState DemoAccount DemoAsset :=
  executeTransfer demoState .alice .bob .rft 40 transfer40_is_funded

def demoBridgeAfterLedger : Ledger DemoLedgerAccount DemoAsset :=
  postJournal demoBridgeLedger
    (holderTransferJournal demoHolderLedgerMap .alice .bob .rft 40)

theorem demoBridgeTransfer_preserves_subledger_agreement :
    HolderSubledgerAgreement demoHolderLedgerMap
      demoBridgeAfterHoldings demoBridgeAfterLedger :=
  holderSubledgerAgreement_transfer demoHolderLedgerMap demoState demoBridgeLedger
    demoHolderSubledgerAgreement .alice .bob .rft 40 transfer40_is_funded

theorem demoBridgeTransfer_preserves_total_signed_balance :
    ∀ asset,
      totalSignedBalance demoBridgeAfterLedger asset =
        totalSignedBalance demoBridgeLedger asset := by
  intro asset
  exact holderTransferJournal_preserves_totalSignedBalance
    demoHolderLedgerMap demoBridgeLedger .alice .bob .rft asset 40

theorem demoBridgeTransfer_journal_balanced :
    ∀ asset,
      (∑ account : DemoLedgerAccount,
        (holderTransferJournal demoHolderLedgerMap .alice .bob DemoAsset.rft 40).posting
          account asset) = 0 := by
  intro asset
  exact holderTransferJournal_balanced
    demoHolderLedgerMap .alice .bob DemoAsset.rft asset 40

theorem demoBridge_alice_subledger_matches :
    demoBridgeAfterLedger.balance .aliceSubledger .rft =
      demoBridgeAfterHoldings.balance .alice .rft :=
  demoBridgeTransfer_preserves_subledger_agreement .alice .rft

theorem demoBridge_bob_subledger_matches :
    demoBridgeAfterLedger.balance .bobSubledger .rft =
      demoBridgeAfterHoldings.balance .bob .rft :=
  demoBridgeTransfer_preserves_subledger_agreement .bob .rft


/-! ## Issuance and burn general-ledger bridge regression tests -/

/-- The demo control account is outside the image of every holder subledger. -/
theorem demoControlIsUnmapped :
    ∀ holder : DemoAccount,
      DemoLedgerAccount.control ≠ demoHolderLedgerMap.ledgerAccount holder := by
  intro holder
  cases holder <;> simp [demoHolderLedgerMap]

def demoBridgeAfterIssueHoldings : HoldingsState DemoAccount DemoAsset :=
  issueToHolder demoBridgeAfterHoldings .treasury DemoAsset.rft 15

def demoBridgeAfterIssueLedger : Ledger DemoLedgerAccount DemoAsset :=
  postJournal demoBridgeAfterLedger
    (holderIssuanceJournal demoHolderLedgerMap
      .control .treasury DemoAsset.rft 15)

theorem demoBridgeAfterIssue_preserves_subledger_agreement :
    HolderSubledgerAgreement demoHolderLedgerMap
      demoBridgeAfterIssueHoldings demoBridgeAfterIssueLedger :=
  holderSubledgerAgreement_issue
    demoHolderLedgerMap
    demoBridgeAfterHoldings
    demoBridgeAfterLedger
    demoBridgeTransfer_preserves_subledger_agreement
    .control
    demoControlIsUnmapped
    .treasury DemoAsset.rft 15

theorem demoBridgeAfterIssue_journal_balanced :
    ∀ asset,
      (∑ account : DemoLedgerAccount,
        (holderIssuanceJournal demoHolderLedgerMap
          .control .treasury DemoAsset.rft 15).posting account asset) = 0 := by
  intro asset
  exact holderIssuanceJournal_balanced
    demoHolderLedgerMap .control .treasury DemoAsset.rft asset 15

theorem demoBridgeAfterIssue_preserves_total_signed_balance :
    ∀ asset,
      totalSignedBalance demoBridgeAfterIssueLedger asset =
        totalSignedBalance demoBridgeAfterLedger asset := by
  intro asset
  exact totalSignedBalance_postJournal demoBridgeAfterLedger
    (holderIssuanceJournal demoHolderLedgerMap .control .treasury DemoAsset.rft 15)
    asset

theorem demoBridgeAfterTransfer_treasury_balance :
    demoBridgeAfterHoldings.balance DemoAccount.treasury DemoAsset.rft = 75 := by
  change afterTransfer.balance DemoAccount.treasury DemoAsset.rft = 75
  exact transfer40_expected_balances.2.2.1

theorem demoBridgeAfterIssue_treasury_balance :
    demoBridgeAfterIssueLedger.balance .treasurySubledger DemoAsset.rft = 90 := by
  have hAgreement :
      demoBridgeAfterIssueLedger.balance .treasurySubledger DemoAsset.rft =
        demoBridgeAfterIssueHoldings.balance DemoAccount.treasury DemoAsset.rft := by
    simpa [demoHolderLedgerMap] using
      (demoBridgeAfterIssue_preserves_subledger_agreement
        DemoAccount.treasury DemoAsset.rft)
  rw [hAgreement]
  change (issueToHolder demoBridgeAfterHoldings
    DemoAccount.treasury DemoAsset.rft 15).balance
      DemoAccount.treasury DemoAsset.rft = 90
  simp [issueToHolder, demoBridgeAfterTransfer_treasury_balance]

theorem demoBridgeAfterIssue_control_balance :
    demoBridgeAfterIssueLedger.balance .control DemoAsset.rft = -15 := by
  decide

theorem demoBridgeAfterIssue_alice_balance :
    demoBridgeAfterIssueHoldings.balance DemoAccount.alice DemoAsset.rft = 60 := by
  change (issueToHolder demoBridgeAfterHoldings
    DemoAccount.treasury DemoAsset.rft 15).balance
      DemoAccount.alice DemoAsset.rft = 60
  have hAlice :
      demoBridgeAfterHoldings.balance DemoAccount.alice DemoAsset.rft = 60 := by
    change afterTransfer.balance DemoAccount.alice DemoAsset.rft = 60
    exact transfer40_expected_balances.1
  simp [issueToHolder, hAlice]

def demoBridgeAfterBurnHoldings : HoldingsState DemoAccount DemoAsset :=
  burnFromHolder demoBridgeAfterIssueHoldings .alice DemoAsset.rft 20

def demoBridgeAfterBurnLedger : Ledger DemoLedgerAccount DemoAsset :=
  postJournal demoBridgeAfterIssueLedger
    (holderBurnJournal demoHolderLedgerMap
      .control .alice DemoAsset.rft 20)

theorem demoBridgeAfterBurn_preserves_subledger_agreement :
    HolderSubledgerAgreement demoHolderLedgerMap
      demoBridgeAfterBurnHoldings demoBridgeAfterBurnLedger :=
  holderSubledgerAgreement_burn
    demoHolderLedgerMap
    demoBridgeAfterIssueHoldings
    demoBridgeAfterIssueLedger
    demoBridgeAfterIssue_preserves_subledger_agreement
    .control
    demoControlIsUnmapped
    .alice DemoAsset.rft 20

theorem demoBridgeAfterBurn_journal_balanced :
    ∀ asset,
      (∑ account : DemoLedgerAccount,
        (holderBurnJournal demoHolderLedgerMap
          .control .alice DemoAsset.rft 20).posting account asset) = 0 := by
  intro asset
  exact holderBurnJournal_balanced
    demoHolderLedgerMap .control .alice DemoAsset.rft asset 20

theorem demoBridgeAfterBurn_preserves_total_signed_balance :
    ∀ asset,
      totalSignedBalance demoBridgeAfterBurnLedger asset =
        totalSignedBalance demoBridgeAfterIssueLedger asset := by
  intro asset
  exact totalSignedBalance_postJournal demoBridgeAfterIssueLedger
    (holderBurnJournal demoHolderLedgerMap .control .alice DemoAsset.rft 20)
    asset

theorem demoBridgeAfterBurn_alice_balance :
    demoBridgeAfterBurnLedger.balance .aliceSubledger DemoAsset.rft = 40 := by
  have hAgreement :
      demoBridgeAfterBurnLedger.balance .aliceSubledger DemoAsset.rft =
        demoBridgeAfterBurnHoldings.balance DemoAccount.alice DemoAsset.rft := by
    simpa [demoHolderLedgerMap] using
      (demoBridgeAfterBurn_preserves_subledger_agreement
        DemoAccount.alice DemoAsset.rft)
  rw [hAgreement]
  change (burnFromHolder demoBridgeAfterIssueHoldings
    DemoAccount.alice DemoAsset.rft 20).balance
      DemoAccount.alice DemoAsset.rft = 40
  norm_num [burnFromHolder, demoBridgeAfterIssue_alice_balance]

theorem demoBridgeAfterBurn_control_balance :
    demoBridgeAfterBurnLedger.balance .control DemoAsset.rft = 5 := by
  decide


/-! ## Abstract authorization policy regression examples

This small policy is intentionally illustrative. It demonstrates the shape
of the authorization gate; it does not select production ownership, key,
role, threshold, or governance rules.
-/

inductive DemoPrincipal
  | alice
  | bob
  | treasury
  | auditor
  deriving DecidableEq, Repr

def demoAuthorizationPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset where
  mayTransfer := fun _state principal source _destination _asset _amount =>
    match principal, source with
    | DemoPrincipal.alice, DemoAccount.alice => True
    | DemoPrincipal.bob, DemoAccount.bob => True
    | DemoPrincipal.treasury, DemoAccount.treasury => True
    | _, _ => False
  mayIssue := fun _state principal _recipient _asset _amount =>
    principal = DemoPrincipal.treasury
  mayBurn := fun _state principal holder _asset _amount =>
    (principal = DemoPrincipal.alice ∧ holder = DemoAccount.alice) ∨
    (principal = DemoPrincipal.bob ∧ holder = DemoAccount.bob) ∨
    (principal = DemoPrincipal.treasury ∧ holder = DemoAccount.treasury)

theorem demoAliceMayTransferFromAlice :
    demoAuthorizationPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob DemoAsset.rft 40 := by
  simp [demoAuthorizationPolicy]

theorem demoTreasuryCannotTransferFromAlice :
    ¬ demoAuthorizationPolicy.mayTransfer demoState
      DemoPrincipal.treasury DemoAccount.alice DemoAccount.bob DemoAsset.rft 40 := by
  simp [demoAuthorizationPolicy]

theorem demoTreasuryMayIssue :
    demoAuthorizationPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAsset.rft 15 := by
  simp [demoAuthorizationPolicy]

theorem demoAliceCannotIssue :
    ¬ demoAuthorizationPolicy.mayIssue demoState
      DemoPrincipal.alice DemoAccount.treasury DemoAsset.rft 15 := by
  simp [demoAuthorizationPolicy]

theorem demoAliceMayBurnOwn :
    demoAuthorizationPolicy.mayBurn demoState
      DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20 := by
  simp [demoAuthorizationPolicy]

theorem demoBobCannotBurnAlice :
    ¬ demoAuthorizationPolicy.mayBurn demoState
      DemoPrincipal.bob DemoAccount.alice DemoAsset.rft 20 := by
  simp [demoAuthorizationPolicy]

def demoAuthorizedAfterTransfer : HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedTransfer demoAuthorizationPolicy demoState
    DemoPrincipal.alice DemoAccount.alice DemoAccount.bob DemoAsset.rft 40
    demoAliceMayTransferFromAlice transfer40_is_funded

theorem demoAuthorizedTransfer_preserves_reconciliation :
    HoldingsInvariant demoAuthorizedAfterTransfer :=
  executeAuthorizedTransfer_preserves_invariant
    demoAuthorizationPolicy demoState demoState_reconciled
    DemoPrincipal.alice DemoAccount.alice DemoAccount.bob DemoAsset.rft 40
    demoAliceMayTransferFromAlice transfer40_is_funded

theorem demoAuthorizedTransfer_matches_existing :
    demoAuthorizedAfterTransfer = afterTransfer := by
  rfl

def demoAuthorizedAfterIssue : HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedIssue demoAuthorizationPolicy demoState
    DemoPrincipal.treasury DemoAccount.treasury DemoAsset.rft 15
    demoTreasuryMayIssue

theorem demoAuthorizedIssue_preserves_reconciliation :
    HoldingsInvariant demoAuthorizedAfterIssue :=
  executeAuthorizedIssue_preserves_invariant
    demoAuthorizationPolicy demoState demoState_reconciled
    DemoPrincipal.treasury DemoAccount.treasury DemoAsset.rft 15
    demoTreasuryMayIssue

theorem demoAuthorizedIssue_matches_existing :
    demoAuthorizedAfterIssue = afterIssue := by
  rfl

def demoAuthorizedAfterBurn : HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedBurn demoAuthorizationPolicy demoState
    DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20
    demoAliceMayBurnOwn alice_rft_can_burn_20

theorem demoAuthorizedBurn_preserves_reconciliation :
    HoldingsInvariant demoAuthorizedAfterBurn :=
  executeAuthorizedBurn_preserves_invariant
    demoAuthorizationPolicy demoState demoState_reconciled
    DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20
    demoAliceMayBurnOwn alice_rft_can_burn_20

theorem demoAuthorizedBurn_matches_existing :
    demoAuthorizedAfterBurn = afterBurn := by
  rfl



/-! ## Reachability through the authorized holder state machine -/

theorem demoTreasuryMayIssueAfterTransfer :
    demoAuthorizationPolicy.mayIssue demoAuthorizedAfterTransfer
      DemoPrincipal.treasury DemoAccount.treasury DemoAsset.rft 15 := by
  simp [demoAuthorizationPolicy]

def demoAuthorizedAfterTransferAndIssue :
    HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedIssue demoAuthorizationPolicy demoAuthorizedAfterTransfer
    DemoPrincipal.treasury DemoAccount.treasury DemoAsset.rft 15
    demoTreasuryMayIssueAfterTransfer

theorem demoAliceMayBurnAfterTransferAndIssue :
    demoAuthorizationPolicy.mayBurn demoAuthorizedAfterTransferAndIssue
      DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20 := by
  simp [demoAuthorizationPolicy]

theorem demoAliceHasFundsAfterTransferAndIssue :
    (20 : Int) ≤
      demoAuthorizedAfterTransferAndIssue.balance
        DemoAccount.alice DemoAsset.rft := by
  change (20 : Int) ≤
    (issueToHolder afterTransfer DemoAccount.treasury DemoAsset.rft 15).balance
      DemoAccount.alice DemoAsset.rft
  have hUnchanged :
      (issueToHolder afterTransfer DemoAccount.treasury DemoAsset.rft 15).balance
          DemoAccount.alice DemoAsset.rft =
        afterTransfer.balance DemoAccount.alice DemoAsset.rft := by
    simp [issueToHolder]
  rw [hUnchanged, transfer40_expected_balances.1]
  norm_num

def demoAuthorizedTraceFinalState :
    HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedBurn demoAuthorizationPolicy
    demoAuthorizedAfterTransferAndIssue
    DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20
    demoAliceMayBurnAfterTransferAndIssue
    demoAliceHasFundsAfterTransferAndIssue

theorem demoAuthorizedTransfer_is_step :
    AuthorizedHolderStep demoAuthorizationPolicy
      demoState demoAuthorizedAfterTransfer := by
  exact Or.inl ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAccount.bob,
    DemoAsset.rft,
    40,
    demoAliceMayTransferFromAlice,
    transfer40_is_funded,
    rfl
  ⟩

theorem demoAuthorizedIssue_is_step :
    AuthorizedHolderStep demoAuthorizationPolicy
      demoAuthorizedAfterTransfer demoAuthorizedAfterTransferAndIssue := by
  exact Or.inr (Or.inl ⟨
    DemoPrincipal.treasury,
    DemoAccount.treasury,
    DemoAsset.rft,
    15,
    demoTreasuryMayIssueAfterTransfer,
    rfl
  ⟩)

theorem demoAuthorizedBurn_is_step :
    AuthorizedHolderStep demoAuthorizationPolicy
      demoAuthorizedAfterTransferAndIssue demoAuthorizedTraceFinalState := by
  exact Or.inr (Or.inr ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAsset.rft,
    20,
    demoAliceMayBurnAfterTransferAndIssue,
    demoAliceHasFundsAfterTransferAndIssue,
    rfl
  ⟩)

def demoAuthorizedHolderMachine :
    VerifiedStateMachine (HoldingsState DemoAccount DemoAsset) :=
  authorizedHolderMachine demoAuthorizationPolicy
    demoState demoState_reconciled

theorem demoAuthorizedInitial_reachable :
    Reachable demoAuthorizedHolderMachine demoState :=
  Reachable.initial rfl

theorem demoAuthorizedTransfer_reachable :
    Reachable demoAuthorizedHolderMachine demoAuthorizedAfterTransfer :=
  Reachable.step demoAuthorizedInitial_reachable
    demoAuthorizedTransfer_is_step

theorem demoAuthorizedIssue_reachable :
    Reachable demoAuthorizedHolderMachine demoAuthorizedAfterTransferAndIssue :=
  Reachable.step demoAuthorizedTransfer_reachable
    demoAuthorizedIssue_is_step

theorem demoAuthorizedTrace_reachable :
    Reachable demoAuthorizedHolderMachine demoAuthorizedTraceFinalState :=
  Reachable.step demoAuthorizedIssue_reachable
    demoAuthorizedBurn_is_step

theorem demoAuthorizedTrace_preserves_reconciliation :
    HoldingsInvariant demoAuthorizedTraceFinalState :=
  holdingsInvariant_of_authorized_reachable
    demoAuthorizationPolicy demoState demoState_reconciled
    demoAuthorizedTrace_reachable


/-! ## Integrated authorized financial state-machine regression -/

/-- Initial state contains both the holder projection and its GL ledger. -/
def demoInitialFinancialState :
    FinancialState DemoAccount DemoLedgerAccount DemoAsset :=
  { holdings := demoState
    ledger := demoBridgeLedger }

theorem demoInitialFinancialState_invariant :
    FinancialInvariant demoHolderLedgerMap demoInitialFinancialState :=
  ⟨demoState_reconciled, demoHolderSubledgerAgreement⟩

/-- The transfer transition updates holder balances and the matching GL journal. -/
def demoFinancialAfterTransfer :
    FinancialState DemoAccount DemoLedgerAccount DemoAsset :=
  { holdings := demoBridgeAfterHoldings
    ledger := demoBridgeAfterLedger }

theorem demoFinancialTransfer_is_authorized_step :
    AuthorizedFinancialStep demoAuthorizationPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoInitialFinancialState demoFinancialAfterTransfer := by
  exact Or.inl ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAccount.bob,
    DemoAsset.rft,
    40,
    demoAliceMayTransferFromAlice,
    transfer40_is_funded,
    rfl
  ⟩

/-- The issuance transition updates the recipient subledger and counterpart. -/
def demoFinancialAfterIssue :
    FinancialState DemoAccount DemoLedgerAccount DemoAsset :=
  { holdings := demoBridgeAfterIssueHoldings
    ledger := demoBridgeAfterIssueLedger }

theorem demoFinancialIssue_is_authorized_step :
    AuthorizedFinancialStep demoAuthorizationPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoFinancialAfterTransfer demoFinancialAfterIssue := by
  exact Or.inr (Or.inl ⟨
    DemoPrincipal.treasury,
    DemoAccount.treasury,
    DemoAsset.rft,
    15,
    demoTreasuryMayIssueAfterTransfer,
    demoControlIsUnmapped,
    rfl
  ⟩)

/-- The burn transition updates the holder balance and the same GL ledger. -/
def demoFinancialAfterBurn :
    FinancialState DemoAccount DemoLedgerAccount DemoAsset :=
  { holdings := demoBridgeAfterBurnHoldings
    ledger := demoBridgeAfterBurnLedger }

theorem demoFinancialBurn_is_authorized_step :
    AuthorizedFinancialStep demoAuthorizationPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoFinancialAfterIssue demoFinancialAfterBurn := by
  exact Or.inr (Or.inr ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAsset.rft,
    20,
    demoAliceMayBurnAfterTransferAndIssue,
    demoAliceHasFundsAfterTransferAndIssue,
    demoControlIsUnmapped,
    rfl
  ⟩)

/-- One machine admits exactly the three previously checked financial steps. -/
def demoIntegratedFinancialMachine :
    VerifiedStateMachine
      (FinancialState DemoAccount DemoLedgerAccount DemoAsset) :=
  authorizedFinancialMachine
    demoAuthorizationPolicy
    demoHolderLedgerMap
    DemoLedgerAccount.control
    demoInitialFinancialState
    demoInitialFinancialState_invariant

theorem demoFinancialInitial_reachable :
    Reachable demoIntegratedFinancialMachine demoInitialFinancialState :=
  Reachable.initial rfl

theorem demoFinancialTransfer_reachable :
    Reachable demoIntegratedFinancialMachine demoFinancialAfterTransfer :=
  Reachable.step demoFinancialInitial_reachable
    demoFinancialTransfer_is_authorized_step

theorem demoFinancialIssue_reachable :
    Reachable demoIntegratedFinancialMachine demoFinancialAfterIssue :=
  Reachable.step demoFinancialTransfer_reachable
    demoFinancialIssue_is_authorized_step

theorem demoFinancialBurn_reachable :
    Reachable demoIntegratedFinancialMachine demoFinancialAfterBurn :=
  Reachable.step demoFinancialIssue_reachable
    demoFinancialBurn_is_authorized_step

/--
The final state of the integrated transfer -> issuance -> burn trace
satisfies both holdings/supply reconciliation and holder/GL subledger agreement.
-/
theorem demoFinancialTrace_preserves_both_invariants :
    FinancialInvariant demoHolderLedgerMap demoFinancialAfterBurn :=
  financialInvariant_of_authorized_reachable
    demoAuthorizationPolicy
    demoHolderLedgerMap
    DemoLedgerAccount.control
    demoInitialFinancialState
    demoInitialFinancialState_invariant
    demoFinancialBurn_reachable

/-- The three balanced journals leave aggregate signed GL totals unchanged. -/
theorem demoFinancialTrace_preserves_total_signed_balance :
    ∀ asset,
      totalSignedBalance demoFinancialAfterBurn.ledger asset =
        totalSignedBalance demoInitialFinancialState.ledger asset := by
  intro asset
  change totalSignedBalance demoBridgeAfterBurnLedger asset =
    totalSignedBalance demoBridgeLedger asset
  calc
    totalSignedBalance demoBridgeAfterBurnLedger asset =
        totalSignedBalance demoBridgeAfterIssueLedger asset :=
      demoBridgeAfterBurn_preserves_total_signed_balance asset
    _ = totalSignedBalance demoBridgeAfterLedger asset :=
      demoBridgeAfterIssue_preserves_total_signed_balance asset
    _ = totalSignedBalance demoBridgeLedger asset :=
      demoBridgeTransfer_preserves_total_signed_balance asset

/-- The final Alice subledger has the expected post-burn amount. -/
theorem demoFinancialTrace_alice_balance :
    demoFinancialAfterBurn.ledger.balance
        DemoLedgerAccount.aliceSubledger DemoAsset.rft = 40 := by
  exact demoBridgeAfterBurn_alice_balance

/-- The final treasury subledger includes the authorized issuance. -/
theorem demoFinancialTrace_treasury_balance :
    demoFinancialAfterBurn.ledger.balance
        DemoLedgerAccount.treasurySubledger DemoAsset.rft = 90 := by
  exact demoBridgeAfterIssue_treasury_balance

/-- The counterpart reflects the net issuance and burn postings. -/
theorem demoFinancialTrace_control_balance :
    demoFinancialAfterBurn.ledger.balance
        DemoLedgerAccount.control DemoAsset.rft = 5 := by
  exact demoBridgeAfterBurn_control_balance


/-! ## Reachable-state aggregate GL conservation -/

def demoIntegratedConservativeFinancialMachine :
    VerifiedStateMachine
      (FinancialState DemoAccount DemoLedgerAccount DemoAsset) :=
  authorizedFinancialMachineWithConservation
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    demoInitialFinancialState demoInitialFinancialState_invariant

theorem demoConservativeInitial_reachable :
    Reachable demoIntegratedConservativeFinancialMachine
      demoInitialFinancialState :=
  Reachable.initial rfl

theorem demoConservativeTransfer_reachable :
    Reachable demoIntegratedConservativeFinancialMachine
      demoFinancialAfterTransfer :=
  Reachable.step demoConservativeInitial_reachable
    demoFinancialTransfer_is_authorized_step

theorem demoConservativeIssue_reachable :
    Reachable demoIntegratedConservativeFinancialMachine
      demoFinancialAfterIssue :=
  Reachable.step demoConservativeTransfer_reachable
    demoFinancialIssue_is_authorized_step

theorem demoConservativeBurn_reachable :
    Reachable demoIntegratedConservativeFinancialMachine
      demoFinancialAfterBurn :=
  Reachable.step demoConservativeIssue_reachable
    demoFinancialBurn_is_authorized_step

/--
The full transfer -> issuance -> burn trace preserves all three invariants:
holder/supply reconciliation, mapped subledger agreement, and aggregate
signed-ledger conservation for every asset.
-/
theorem demoFinancialTrace_preserves_complete_invariant :
    FinancialConservationInvariant demoHolderLedgerMap
      demoInitialFinancialState.ledger demoFinancialAfterBurn :=
  financialConservationInvariant_of_authorized_reachable
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    demoInitialFinancialState demoInitialFinancialState_invariant
    demoConservativeBurn_reachable

theorem demoFinancialTrace_GL_total_from_machine :
    ∀ asset,
      totalSignedBalance demoFinancialAfterBurn.ledger asset =
        totalSignedBalance demoInitialFinancialState.ledger asset :=
  demoFinancialTrace_preserves_complete_invariant.2

end SIRMTests
