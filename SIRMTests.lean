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
  mayIssue := fun _state principal _issuer _recipient _asset _amount =>
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
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15 := by
  simp [demoAuthorizationPolicy]

theorem demoAliceCannotIssue :
    ¬ demoAuthorizationPolicy.mayIssue demoState
      DemoPrincipal.alice DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15 := by
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
    DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15
    demoTreasuryMayIssue

theorem demoAuthorizedIssue_preserves_reconciliation :
    HoldingsInvariant demoAuthorizedAfterIssue :=
  executeAuthorizedIssue_preserves_invariant
    demoAuthorizationPolicy demoState demoState_reconciled
    DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15
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
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15 := by
  simp [demoAuthorizationPolicy]

def demoAuthorizedAfterTransferAndIssue :
    HoldingsState DemoAccount DemoAsset :=
  executeAuthorizedIssue demoAuthorizationPolicy demoAuthorizedAfterTransfer
    DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury DemoAsset.rft 15
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



/-! ## Authority Registry v1 regression

The registry below gives three exact operation grants:
Alice may transfer Alice -> Bob, Treasury may issue to Treasury,
and Alice may burn from Alice. The amount limits are per operation.
-/

def registryTransferGrant :
    AuthorityGrant DemoPrincipal DemoAccount DemoAsset :=
  { principal := .alice
    scope := .transfer .alice .bob
    asset := .rft
    maxAmount := 100 }

def registryIssueGrant :
    AuthorityGrant DemoPrincipal DemoAccount DemoAsset :=
  { principal := .treasury
    scope := .issue .treasury .treasury
    asset := .rft
    maxAmount := 50 }

def registryBurnGrant :
    AuthorityGrant DemoPrincipal DemoAccount DemoAsset :=
  { principal := .alice
    scope := .burn .alice
    asset := .rft
    maxAmount := 20 }

/--
A key consists of principal, exact operation scope, and asset.
The only two grants belonging to Alice have different scopes.
-/
def demoAuthorityRegistry :
    AuthorityRegistry DemoPrincipal DemoAccount DemoAsset where
  grants := [
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]
  unique_scope := by
    intro left right hLeftMem hRightMem hPrincipal hScope hAsset
    change left ∈
      [registryTransferGrant, registryIssueGrant, registryBurnGrant] at hLeftMem
    change right ∈
      [registryTransferGrant, registryIssueGrant, registryBurnGrant] at hRightMem
    simp only [List.mem_cons, List.not_mem_nil] at hLeftMem hRightMem
    rcases hLeftMem with rfl | rfl | rfl | hLeftFalse
    all_goals
      rcases hRightMem with rfl | rfl | rfl | hRightFalse
    all_goals
      simp_all [
        registryTransferGrant,
        registryIssueGrant,
        registryBurnGrant
      ]

def demoRegistryPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset :=
  AuthorityRegistry.toAuthorizationPolicy demoAuthorityRegistry


def demoAccountControlRegistry :
    AccountControlRegistry DemoPrincipal DemoAccount where
  entries := [
    (DemoPrincipal.alice, DemoAccount.alice),
    (DemoPrincipal.bob, DemoAccount.bob),
    (DemoPrincipal.treasury, DemoAccount.treasury)
  ]

def demoControlledRegistryPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset :=
  toControlledAuthorizationPolicy demoAccountControlRegistry demoAuthorityRegistry

/-! ### Positive authorization cases -/

theorem registryAliceMayTransfer :
    demoRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob
      DemoAsset.rft 40 := by
  change AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.transfer .alice .bob) .rft 40
  exact ⟨
    registryTransferGrant,
    by simp [demoAuthorityRegistry],
    rfl, rfl, rfl,
    by decide
  ⟩

theorem registryTreasuryMayIssue :
    demoRegistryPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury
      DemoAsset.rft 15 := by
  change AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.treasury (.issue .treasury .treasury) .rft 15
  exact ⟨
    registryIssueGrant,
    by simp [demoAuthorityRegistry],
    rfl, rfl, rfl,
    by decide
  ⟩

theorem registryAliceMayBurn :
    demoRegistryPolicy.mayBurn demoState
      DemoPrincipal.alice DemoAccount.alice
      DemoAsset.rft 20 := by
  change AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.burn .alice) .rft 20
  exact ⟨
    registryBurnGrant,
    by simp [demoAuthorityRegistry],
    rfl, rfl, rfl,
    by decide
  ⟩

/-! ### Independent account-control gate -/

theorem controlledRegistryAliceMayTransfer :
    demoControlledRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob
      DemoAsset.rft 40 := by
  change AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.alice DemoAccount.alice ∧
    AuthorityRegistry.allows demoAuthorityRegistry
      DemoPrincipal.alice (.transfer .alice .bob) .rft 40
  exact ⟨
    by simp [AccountControlRegistry.controls, demoAccountControlRegistry],
    registryAliceMayTransfer
  ⟩

theorem controlledRegistryTreasuryMayIssue :
    demoControlledRegistryPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury
      DemoAsset.rft 15 := by
  change AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.treasury DemoAccount.treasury ∧
    AuthorityRegistry.allows demoAuthorityRegistry
      DemoPrincipal.treasury (.issue .treasury .treasury) .rft 15
  exact ⟨
    by simp [AccountControlRegistry.controls, demoAccountControlRegistry],
    registryTreasuryMayIssue
  ⟩

theorem controlledRegistryAliceMayBurn :
    demoControlledRegistryPolicy.mayBurn demoState
      DemoPrincipal.alice DemoAccount.alice DemoAsset.rft 20 := by
  change AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.alice DemoAccount.alice ∧
    AuthorityRegistry.allows demoAuthorityRegistry
      DemoPrincipal.alice (.burn .alice) .rft 20
  exact ⟨
    by simp [AccountControlRegistry.controls, demoAccountControlRegistry],
    registryAliceMayBurn
  ⟩

def demoEmptyAccountControlRegistry :
    AccountControlRegistry DemoPrincipal DemoAccount where
  entries := []

def demoNoControlRegistryPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset :=
  toControlledAuthorizationPolicy demoEmptyAccountControlRegistry
    demoAuthorityRegistry

theorem registryGrantWithoutAccountControlIsDenied :
    ¬ demoNoControlRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob
      DemoAsset.rft 40 := by
  change ¬ (
    AccountControlRegistry.controls demoEmptyAccountControlRegistry
      DemoPrincipal.alice DemoAccount.alice ∧
    AuthorityRegistry.allows demoAuthorityRegistry
      DemoPrincipal.alice (.transfer .alice .bob) .rft 40)
  simp [AccountControlRegistry.controls, demoEmptyAccountControlRegistry]

theorem registryAccountControlWithoutGrantIsDenied :
    ¬ demoControlledRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.treasury
      DemoAsset.rft 40 := by
  change ¬ (
    AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.alice DemoAccount.alice ∧
    AuthorityRegistry.allows demoAuthorityRegistry
      DemoPrincipal.alice (.transfer .alice .treasury) .rft 40)
  simp [
    AccountControlRegistry.controls,
    demoAccountControlRegistry,
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

/-- Treasury controls the issuer account, but not Alice's recipient account. -/
theorem treasuryDoesNotControlAlice :
    ¬ AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.treasury DemoAccount.alice := by
  simp [AccountControlRegistry.controls, demoAccountControlRegistry]

def registryIssueToAliceGrant :
    AuthorityGrant DemoPrincipal DemoAccount DemoAsset :=
  { principal := .treasury
    scope := .issue .treasury .alice
    asset := .rft
    maxAmount := 25 }

def demoIssueToAliceAuthorityRegistry :
    AuthorityRegistry DemoPrincipal DemoAccount DemoAsset where
  grants := [registryIssueToAliceGrant]
  unique_scope := by
    intro left right hLeftMem hRightMem _ _ _
    have hLeft : left = registryIssueToAliceGrant := by
      simpa using hLeftMem
    have hRight : right = registryIssueToAliceGrant := by
      simpa using hRightMem
    rw [hLeft, hRight]

def demoTreasuryIssueToUncontrolledRecipientPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset :=
  toControlledAuthorizationPolicy demoAccountControlRegistry
    demoIssueToAliceAuthorityRegistry

theorem controlledTreasuryMayIssueToUncontrolledAlice :
    demoTreasuryIssueToUncontrolledRecipientPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.alice
      DemoAsset.rft 15 := by
  change AccountControlRegistry.controls demoAccountControlRegistry
      DemoPrincipal.treasury DemoAccount.treasury ∧
    AuthorityRegistry.allows demoIssueToAliceAuthorityRegistry
      DemoPrincipal.treasury (.issue .treasury .alice) .rft 15
  exact ⟨
    by simp [AccountControlRegistry.controls, demoAccountControlRegistry],
    ⟨
      registryIssueToAliceGrant,
      by simp [demoIssueToAliceAuthorityRegistry],
      rfl, rfl, rfl,
      by decide
    ⟩
  ⟩

/-! ### Negative authorization cases -/

theorem registryAliceCannotExceedTransferLimit :
    ¬ demoRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob
      DemoAsset.rft 101 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.transfer .alice .bob) .rft 101
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryCannotChangeTransferDestination :
    ¬ demoRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.treasury
      DemoAsset.rft 40 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.transfer .alice .treasury) .rft 40
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryCannotReverseTransferDirection :
    ¬ demoRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.bob DemoAccount.alice
      DemoAsset.rft 40 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.transfer .bob .alice) .rft 40
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryCannotUseAnotherAsset :
    ¬ demoRegistryPolicy.mayTransfer demoState
      DemoPrincipal.alice DemoAccount.alice DemoAccount.bob
      DemoAsset.usd 40 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.transfer .alice .bob) .usd 40
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryAliceCannotIssue :
    ¬ demoRegistryPolicy.mayIssue demoState
      DemoPrincipal.alice DemoAccount.treasury DemoAccount.treasury
      DemoAsset.rft 15 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.issue .treasury .treasury) .rft 15
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryTreasuryCannotExceedIssueLimit :
    ¬ demoRegistryPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.treasury
      DemoAsset.rft 51 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.treasury (.issue .treasury .treasury) .rft 51
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryTreasuryCannotIssueToAlice :
    ¬ demoRegistryPolicy.mayIssue demoState
      DemoPrincipal.treasury DemoAccount.treasury DemoAccount.alice
      DemoAsset.rft 15 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.treasury (.issue .treasury .alice) .rft 15
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryBobCannotBurnAlice :
    ¬ demoRegistryPolicy.mayBurn demoState
      DemoPrincipal.bob DemoAccount.alice
      DemoAsset.rft 20 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.bob (.burn .alice) .rft 20
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

theorem registryAliceCannotExceedBurnLimit :
    ¬ demoRegistryPolicy.mayBurn demoState
      DemoPrincipal.alice DemoAccount.alice
      DemoAsset.rft 21 := by
  change ¬ AuthorityRegistry.allows demoAuthorityRegistry
    DemoPrincipal.alice (.burn .alice) .rft 21
  simp [
    AuthorityRegistry.allows,
    demoAuthorityRegistry,
    registryTransferGrant,
    registryIssueGrant,
    registryBurnGrant
  ]

/-! ### Integration with the existing financial state machine -/

theorem registryFinancialTransfer_is_step :
    AuthorizedFinancialStep demoControlledRegistryPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoInitialFinancialState demoFinancialAfterTransfer := by
  exact Or.inl ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAccount.bob,
    DemoAsset.rft,
    40,
    controlledRegistryAliceMayTransfer,
    transfer40_is_funded,
    rfl
  ⟩

theorem registryFinancialIssue_is_step :
    AuthorizedFinancialStep demoControlledRegistryPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoFinancialAfterTransfer demoFinancialAfterIssue := by
  exact Or.inr (Or.inl ⟨
    DemoPrincipal.treasury,
    DemoAccount.treasury,
    DemoAccount.treasury,
    DemoAsset.rft,
    15,
    controlledRegistryTreasuryMayIssue,
    demoControlIsUnmapped,
    rfl
  ⟩)

theorem registryFinancialBurn_is_step :
    AuthorizedFinancialStep demoControlledRegistryPolicy demoHolderLedgerMap
      DemoLedgerAccount.control
      demoFinancialAfterIssue demoFinancialAfterBurn := by
  exact Or.inr (Or.inr ⟨
    DemoPrincipal.alice,
    DemoAccount.alice,
    DemoAsset.rft,
    20,
    controlledRegistryAliceMayBurn,
    demoAliceHasFundsAfterTransferAndIssue,
    demoControlIsUnmapped,
    rfl
  ⟩)

def demoRegistryFinancialMachine :
    VerifiedStateMachine
      (FinancialState DemoAccount DemoLedgerAccount DemoAsset) :=
  authorizedFinancialMachineWithConservation
    demoControlledRegistryPolicy
    demoHolderLedgerMap
    DemoLedgerAccount.control
    demoInitialFinancialState
    demoInitialFinancialState_invariant

theorem registryFinancialInitial_reachable :
    Reachable demoRegistryFinancialMachine demoInitialFinancialState :=
  Reachable.initial rfl

theorem registryFinancialTransfer_reachable :
    Reachable demoRegistryFinancialMachine demoFinancialAfterTransfer :=
  Reachable.step registryFinancialInitial_reachable
    registryFinancialTransfer_is_step

theorem registryFinancialIssue_reachable :
    Reachable demoRegistryFinancialMachine demoFinancialAfterIssue :=
  Reachable.step registryFinancialTransfer_reachable
    registryFinancialIssue_is_step

theorem registryFinancialBurn_reachable :
    Reachable demoRegistryFinancialMachine demoFinancialAfterBurn :=
  Reachable.step registryFinancialIssue_reachable
    registryFinancialBurn_is_step

/--
The registry-backed financial trace preserves holder/supply reconciliation,
mapped subledger agreement, and aggregate signed-ledger conservation.
-/
theorem registryFinancialTrace_preserves_complete_invariant :
    FinancialConservationInvariant demoHolderLedgerMap
      demoInitialFinancialState.ledger demoFinancialAfterBurn :=
  financialConservationInvariant_of_authorized_reachable
    demoControlledRegistryPolicy
    demoHolderLedgerMap
    DemoLedgerAccount.control
    demoInitialFinancialState
    demoInitialFinancialState_invariant
    registryFinancialBurn_reachable


/-! ## Typed account and asset registry regressions -/

def typedDemoNetwork : NetworkId := ⟨7⟩

def typedDemoTreasury : AccountId 2 := ⟨0⟩

def typedDemoCustomer : AccountId 2 := ⟨1⟩

def typedDemoAccountRegistry : AccountRegistry 2 where
  metadata := fun account =>
    if account = typedDemoTreasury then
      { accountKind := .treasury
        status := .active
        network := typedDemoNetwork }
    else
      { accountKind := .holder
        status := .active
        network := typedDemoNetwork }

def typedDemoAsset : AssetId 1 := ⟨0⟩

def typedDemoAssetMetadata : AssetMetadata 2 where
  symbol := "TST"
  decimals := 2
  issuer := typedDemoTreasury
  status := .active
  network := typedDemoNetwork

def typedDemoAssetRegistry :
    AssetRegistry 2 1 typedDemoAccountRegistry where
  metadata := fun _ => typedDemoAssetMetadata
  issuer_network_matches := by
    intro asset
    simp [typedDemoAssetMetadata, typedDemoAccountRegistry,
      typedDemoTreasury]

theorem typedRegistry_treasury_class_is_preserved :
    typedDemoAccountRegistry.classOf typedDemoTreasury =
      AccountClass.treasury := by
  simp [AccountRegistry.classOf, typedDemoAccountRegistry,
    typedDemoTreasury]

theorem typedRegistry_asset_uses_demo_decimal_scale :
    typedDemoAssetMetadata.baseUnitsPerWhole = 100 := by
  norm_num [AssetMetadata.baseUnitsPerWhole, typedDemoAssetMetadata]

theorem typedRegistry_asset_issuer_network_matches :
    (typedDemoAssetRegistry.metadata typedDemoAsset).network =
      (typedDemoAccountRegistry.metadata
        (typedDemoAssetRegistry.metadata typedDemoAsset).issuer).network :=
  typedDemoAssetRegistry.issuer_network_matches typedDemoAsset

theorem typedRegistry_active_asset_and_issuer_enable_issuance :
    typedDemoAssetRegistry.issuanceEnabled typedDemoAsset := by
  simp [AssetRegistry.issuanceEnabled, AssetRegistry.isActive,
    AccountRegistry.isActive, typedDemoAssetRegistry,
    typedDemoAssetMetadata, typedDemoAccountRegistry,
    typedDemoTreasury]

def typedDemoDraftAssetMetadata : AssetMetadata 2 :=
  { typedDemoAssetMetadata with status := .draft }

def typedDemoDraftAssetRegistry :
    AssetRegistry 2 1 typedDemoAccountRegistry where
  metadata := fun _ => typedDemoDraftAssetMetadata
  issuer_network_matches := by
    intro asset
    simp [typedDemoDraftAssetMetadata, typedDemoAssetMetadata,
      typedDemoAccountRegistry, typedDemoTreasury]

theorem typedRegistry_draft_asset_blocks_issuance :
    ¬ typedDemoDraftAssetRegistry.issuanceEnabled typedDemoAsset := by
  simp [AssetRegistry.issuanceEnabled, AssetRegistry.isActive,
    AccountRegistry.isActive, typedDemoDraftAssetRegistry,
    typedDemoDraftAssetMetadata, typedDemoAssetMetadata,
    typedDemoAccountRegistry, typedDemoTreasury]

def typedDemoFrozenIssuerAccounts : AccountRegistry 2 where
  metadata := fun account =>
    if account = typedDemoTreasury then
      { accountKind := .treasury
        status := .frozen
        network := typedDemoNetwork }
    else
      { accountKind := .holder
        status := .active
        network := typedDemoNetwork }

def typedDemoFrozenIssuerAssets :
    AssetRegistry 2 1 typedDemoFrozenIssuerAccounts where
  metadata := fun _ => typedDemoAssetMetadata
  issuer_network_matches := by
    intro asset
    simp [typedDemoAssetMetadata, typedDemoFrozenIssuerAccounts,
      typedDemoTreasury]

theorem typedRegistry_frozen_issuer_blocks_issuance :
    ¬ typedDemoFrozenIssuerAssets.issuanceEnabled typedDemoAsset := by
  simp [AssetRegistry.issuanceEnabled, AssetRegistry.isActive,
    AccountRegistry.isActive, typedDemoFrozenIssuerAssets,
    typedDemoFrozenIssuerAccounts, typedDemoAssetMetadata,
    typedDemoTreasury]

theorem typedRegistry_empty_holdings_preserves_existing_model :
    HoldingsInvariant
      (emptyHoldingsState (AccountId 2) (AssetId 1)) :=
  typedEmptyHoldingsState_invariant 2 1

/-! ## Registry-aware issuance financial-machine regressions -/

def typedDemoIssueGrant :
    AuthorityGrant DemoPrincipal (AccountId 2) (AssetId 1) :=
  { principal := .treasury
    scope := .issue typedDemoTreasury typedDemoCustomer
    asset := typedDemoAsset
    maxAmount := 15 }

def typedDemoIssueAuthorityRegistry :
    AuthorityRegistry DemoPrincipal (AccountId 2) (AssetId 1) where
  grants := [typedDemoIssueGrant]
  unique_scope := by
    intro left right hLeftMem hRightMem _ _ _
    have hLeft : left = typedDemoIssueGrant := by
      simpa using hLeftMem
    have hRight : right = typedDemoIssueGrant := by
      simpa using hRightMem
    rw [hLeft, hRight]

def typedDemoAccountControlRegistry :
    AccountControlRegistry DemoPrincipal (AccountId 2) where
  entries := [(DemoPrincipal.treasury, typedDemoTreasury)]

def typedDemoControlledPolicy :
    AuthorizationPolicy DemoPrincipal (AccountId 2) (AssetId 1) :=
  toControlledAuthorizationPolicy
    typedDemoAccountControlRegistry typedDemoIssueAuthorityRegistry

theorem typedDemoBasePolicyMayIssue :
    typedDemoControlledPolicy.mayIssue
      (emptyHoldingsState (AccountId 2) (AssetId 1))
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 := by
  change AccountControlRegistry.controls typedDemoAccountControlRegistry
      DemoPrincipal.treasury typedDemoTreasury ∧
    AuthorityRegistry.allows typedDemoIssueAuthorityRegistry
      DemoPrincipal.treasury
      (.issue typedDemoTreasury typedDemoCustomer) typedDemoAsset 15
  exact ⟨
    by simp [AccountControlRegistry.controls, typedDemoAccountControlRegistry],
    ⟨typedDemoIssueGrant, by simp [typedDemoIssueAuthorityRegistry],
      rfl, rfl, rfl, by decide⟩
  ⟩

def typedDemoRegistryAwarePolicy :
    AuthorizationPolicy DemoPrincipal (AccountId 2) (AssetId 1) :=
  withAssetRegistryIssuanceGate
    typedDemoControlledPolicy typedDemoAssetRegistry

theorem typedDemoRegistryAwareMayIssue :
    typedDemoRegistryAwarePolicy.mayIssue
      (emptyHoldingsState (AccountId 2) (AssetId 1))
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 := by
  change typedDemoControlledPolicy.mayIssue
      (emptyHoldingsState (AccountId 2) (AssetId 1))
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 ∧
    typedDemoAssetRegistry.issuanceEnabled typedDemoAsset
  exact ⟨typedDemoBasePolicyMayIssue,
    typedRegistry_active_asset_and_issuer_enable_issuance⟩

theorem typedDemoDraftAssetBlocksRegistryAwareIssue :
    ¬ (withAssetRegistryIssuanceGate
        typedDemoControlledPolicy typedDemoDraftAssetRegistry).mayIssue
      (emptyHoldingsState (AccountId 2) (AssetId 1))
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 := by
  rw [withAssetRegistryIssuanceGate_mayIssue_iff]
  rintro ⟨_, hEnabled⟩
  exact typedRegistry_draft_asset_blocks_issuance hEnabled

theorem typedDemoFrozenIssuerBlocksRegistryAwareIssue :
    ¬ (withAssetRegistryIssuanceGate
        typedDemoControlledPolicy typedDemoFrozenIssuerAssets).mayIssue
      (emptyHoldingsState (AccountId 2) (AssetId 1))
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 := by
  rw [withAssetRegistryIssuanceGate_mayIssue_iff]
  rintro ⟨_, hEnabled⟩
  exact typedRegistry_frozen_issuer_blocks_issuance hEnabled

theorem typedDemoRegistryGateLeavesTransferUnchanged
    (state : HoldingsState (AccountId 2) (AssetId 1))
    (principal : DemoPrincipal)
    (source destination : AccountId 2)
    (asset : AssetId 1) (amount : Nat) :
    typedDemoRegistryAwarePolicy.mayTransfer
        state principal source destination asset amount ↔
      typedDemoControlledPolicy.mayTransfer
        state principal source destination asset amount :=
  withAssetRegistryIssuanceGate_mayTransfer_iff
    typedDemoControlledPolicy typedDemoAssetRegistry
    state principal source destination asset amount

theorem typedDemoRegistryGateLeavesBurnUnchanged
    (state : HoldingsState (AccountId 2) (AssetId 1))
    (principal : DemoPrincipal)
    (holder : AccountId 2)
    (asset : AssetId 1) (amount : Nat) :
    typedDemoRegistryAwarePolicy.mayBurn
        state principal holder asset amount ↔
      typedDemoControlledPolicy.mayBurn
        state principal holder asset amount :=
  withAssetRegistryIssuanceGate_mayBurn_iff
    typedDemoControlledPolicy typedDemoAssetRegistry
    state principal holder asset amount

/-- `some holder` is the holder subledger; `none` is the unmapped counterpart. -/
def typedDemoHolderLedgerMap :
    HolderLedgerMap (AccountId 2) (Option (AccountId 2)) where
  ledgerAccount := some
  injective_ledgerAccount := by
    intro left right h
    injection h

theorem typedDemoControlIsUnmapped :
    ∀ holder : AccountId 2,
      (none : Option (AccountId 2)) ≠
        typedDemoHolderLedgerMap.ledgerAccount holder := by
  intro holder
  simp [typedDemoHolderLedgerMap]

def typedDemoInitialFinancialState :
    FinancialState (AccountId 2) (Option (AccountId 2)) (AssetId 1) :=
  { holdings := emptyHoldingsState (AccountId 2) (AssetId 1)
    ledger := ⟨fun _ _ => 0⟩ }

theorem typedDemoInitialFinancialState_invariant :
    FinancialInvariant typedDemoHolderLedgerMap
      typedDemoInitialFinancialState := by
  constructor
  · exact typedEmptyHoldingsState_invariant 2 1
  · intro holder asset
    simp [typedDemoInitialFinancialState, typedDemoHolderLedgerMap,
      emptyHoldingsState]

def typedDemoFinancialAfterIssue :
    FinancialState (AccountId 2) (Option (AccountId 2)) (AssetId 1) :=
  { holdings := executeAuthorizedIssue
      typedDemoRegistryAwarePolicy typedDemoInitialFinancialState.holdings
      DemoPrincipal.treasury typedDemoTreasury typedDemoCustomer
      typedDemoAsset 15 typedDemoRegistryAwareMayIssue
    ledger := postJournal typedDemoInitialFinancialState.ledger
      (holderIssuanceJournal typedDemoHolderLedgerMap
        (none : Option (AccountId 2)) typedDemoCustomer typedDemoAsset 15) }

theorem typedDemoRegistryAwareIssue_is_step :
    AuthorizedFinancialStep typedDemoRegistryAwarePolicy
      typedDemoHolderLedgerMap (none : Option (AccountId 2))
      typedDemoInitialFinancialState typedDemoFinancialAfterIssue := by
  exact Or.inr (Or.inl ⟨
    DemoPrincipal.treasury,
    typedDemoTreasury,
    typedDemoCustomer,
    typedDemoAsset,
    15,
    typedDemoRegistryAwareMayIssue,
    typedDemoControlIsUnmapped,
    rfl
  ⟩)

def typedDemoRegistryAwareMachine :
    VerifiedStateMachine
      (FinancialState (AccountId 2) (Option (AccountId 2)) (AssetId 1)) :=
  registryAwareAuthorizedFinancialMachine
    typedDemoControlledPolicy typedDemoAssetRegistry
    typedDemoHolderLedgerMap (none : Option (AccountId 2))
    typedDemoInitialFinancialState typedDemoInitialFinancialState_invariant

theorem typedDemoRegistryAwareInitial_reachable :
    Reachable typedDemoRegistryAwareMachine typedDemoInitialFinancialState :=
  Reachable.initial rfl

theorem typedDemoRegistryAwareIssue_reachable :
    Reachable typedDemoRegistryAwareMachine typedDemoFinancialAfterIssue :=
  Reachable.step typedDemoRegistryAwareInitial_reachable
    typedDemoRegistryAwareIssue_is_step

theorem typedDemoRegistryAwareTrace_preserves_complete_invariant :
    FinancialConservationInvariant typedDemoHolderLedgerMap
      typedDemoInitialFinancialState.ledger typedDemoFinancialAfterIssue :=
  registryAwareFinancialConservationInvariant_of_reachable
    typedDemoControlledPolicy typedDemoAssetRegistry
    typedDemoHolderLedgerMap (none : Option (AccountId 2))
    typedDemoInitialFinancialState typedDemoInitialFinancialState_invariant
    typedDemoRegistryAwareIssue_reachable


/-! ## Exact asset-denominated base-unit regressions -/

theorem typedRegistry_whole_units_convert_to_base_units :
    typedDemoAssetMetadata.wholeUnitsToBaseUnits 12 = 1200 := by
  norm_num [AssetMetadata.wholeUnitsToBaseUnits,
    AssetMetadata.baseUnitsPerWhole, typedDemoAssetMetadata]

theorem typedRegistry_whole_units_decimal_input_is_exact :
    typedDemoAssetMetadata.toBaseUnits? ⟨12, 0⟩ = some 1200 := by
  norm_num [AssetMetadata.toBaseUnits?, typedDemoAssetMetadata]

theorem typedRegistry_input_at_asset_precision_is_identity :
    typedDemoAssetMetadata.toBaseUnits? ⟨1234, 2⟩ = some 1234 := by
  simp [AssetMetadata.toBaseUnits?, typedDemoAssetMetadata]

theorem typedRegistry_extra_trailing_zero_is_exact :
    typedDemoAssetMetadata.toBaseUnits? ⟨1230, 3⟩ = some 123 := by
  norm_num [AssetMetadata.toBaseUnits?, typedDemoAssetMetadata]

theorem typedRegistry_nonzero_excess_precision_is_rejected :
    typedDemoAssetMetadata.toBaseUnits? ⟨1234, 3⟩ = none := by
  norm_num [AssetMetadata.toBaseUnits?, typedDemoAssetMetadata]

theorem typedRegistry_base_units_fit_explicit_bound :
    typedDemoAssetMetadata.toBaseUnitsWithin? ⟨1230, 3⟩ 123 =
      some ⟨123, by decide⟩ := by
  norm_num [AssetMetadata.toBaseUnitsWithin?, AssetMetadata.toBaseUnits?,
    typedDemoAssetMetadata]

theorem typedRegistry_base_units_above_explicit_bound_are_rejected :
    typedDemoAssetMetadata.toBaseUnitsWithin? ⟨1230, 3⟩ 122 = none := by
  norm_num [AssetMetadata.toBaseUnitsWithin?, AssetMetadata.toBaseUnits?,
    typedDemoAssetMetadata]

/-! ## Exact cross-network migration and dust regressions -/

def demoAssetMigrationRate : AssetMigrationRate where
  numerator := 2
  denominator := 3
  numerator_pos := by decide
  denominator_pos := by decide

inductive DemoMigrationPartition where
  | alice
  | bob
  deriving DecidableEq, Repr

def demoAliceMigrationDustAfterOne :
    AssetMigrationDustState demoAssetMigrationRate
      DemoMigrationPartition .alice :=
  (AssetMigrationDustState.empty demoAssetMigrationRate
    DemoMigrationPartition.alice).addSource 1

def demoAliceMigrationDustAfterTwo :
    AssetMigrationDustState demoAssetMigrationRate
      DemoMigrationPartition .alice :=
  demoAliceMigrationDustAfterOne.addSource 1

def demoBobMigrationDustAfterOne :
    AssetMigrationDustState demoAssetMigrationRate
      DemoMigrationPartition .bob :=
  (AssetMigrationDustState.empty demoAssetMigrationRate
    DemoMigrationPartition.bob).addSource 1

theorem migration_single_source_unit_keeps_fractional_dust :
    demoAliceMigrationDustAfterOne.totalTargetBaseUnits = 0 ∧
      demoAliceMigrationDustAfterOne.dustNumerator = 2 := by
  norm_num [demoAliceMigrationDustAfterOne,
    AssetMigrationDustState.addSource, AssetMigrationDustState.empty,
    demoAssetMigrationRate]

theorem migration_second_source_unit_releases_one_target_unit :
    demoAliceMigrationDustAfterTwo.totalTargetBaseUnits = 1 ∧
      demoAliceMigrationDustAfterTwo.dustNumerator = 1 := by
  norm_num [demoAliceMigrationDustAfterTwo,
    demoAliceMigrationDustAfterOne, AssetMigrationDustState.addSource,
    AssetMigrationDustState.empty, demoAssetMigrationRate]

theorem migration_cumulative_scaled_value_is_conserved :
    demoAliceMigrationDustAfterTwo.totalSourceBaseUnits * 2 =
      demoAliceMigrationDustAfterTwo.totalTargetBaseUnits * 3 +
        demoAliceMigrationDustAfterTwo.dustNumerator := by
  exact demoAliceMigrationDustAfterTwo.scaled_conservation

theorem migration_dust_is_bounded_by_rate_denominator :
    demoAliceMigrationDustAfterTwo.dustNumerator < 3 := by
  exact demoAliceMigrationDustAfterTwo.dust_lt_denominator

theorem migration_bob_has_an_independent_dust_partition :
    demoBobMigrationDustAfterOne.totalTargetBaseUnits = 0 ∧
      demoBobMigrationDustAfterOne.dustNumerator = 2 := by
  norm_num [demoBobMigrationDustAfterOne,
    AssetMigrationDustState.addSource, AssetMigrationDustState.empty,
    demoAssetMigrationRate]

/-- A synthetic second network and issuer for route-eligibility regressions. -/
def demoMigrationOtherNetwork : NetworkId := ⟨8⟩

def demoMigrationAccountRegistry : AccountRegistry 2 where
  metadata := fun account =>
    if account = typedDemoTreasury then
      { accountKind := .treasury
        status := .active
        network := typedDemoNetwork }
    else
      { accountKind := .holder
        status := .active
        network := demoMigrationOtherNetwork }

def demoMigrationSourceMetadata : AssetMetadata 2 :=
  typedDemoAssetMetadata

def demoMigrationDestinationMetadata : AssetMetadata 2 where
  symbol := "DST"
  decimals := 3
  issuer := typedDemoCustomer
  status := .active
  network := demoMigrationOtherNetwork

def demoMigrationAssetRegistry :
    AssetRegistry 2 2 demoMigrationAccountRegistry where
  metadata := fun asset =>
    if asset.index.val = 0 then
      demoMigrationSourceMetadata
    else
      demoMigrationDestinationMetadata
  issuer_network_matches := by
    intro asset
    rcases asset with ⟨i⟩
    fin_cases i
    · simp [demoMigrationSourceMetadata, typedDemoAssetMetadata,
        demoMigrationAccountRegistry, typedDemoTreasury, typedDemoNetwork]
    · simp [demoMigrationDestinationMetadata,
        demoMigrationAccountRegistry, typedDemoTreasury, typedDemoCustomer,
        demoMigrationOtherNetwork]

def demoMigrationSourceAsset : AssetId 2 := ⟨0⟩
def demoMigrationDestinationAsset : AssetId 2 := ⟨1⟩

def demoCrossNetworkMigrationRoute :
    AssetMigrationRoute demoMigrationAssetRegistry where
  sourceAsset := demoMigrationSourceAsset
  destinationAsset := demoMigrationDestinationAsset
  rate := demoAssetMigrationRate
  assets_distinct := by decide
  networks_distinct := by
    change
      (demoMigrationAssetRegistry.metadata (⟨0⟩ : AssetId 2)).network ≠
        (demoMigrationAssetRegistry.metadata (⟨1⟩ : AssetId 2)).network
    decide

theorem migration_demo_route_connects_distinct_networks :
    (demoMigrationAssetRegistry.metadata
      demoCrossNetworkMigrationRoute.sourceAsset).network ≠
    (demoMigrationAssetRegistry.metadata
      demoCrossNetworkMigrationRoute.destinationAsset).network :=
  demoCrossNetworkMigrationRoute.networks_distinct

theorem migration_demo_route_requires_active_endpoints :
    demoCrossNetworkMigrationRoute.endpointsEnabled := by
  change
    (((demoMigrationAssetRegistry.metadata demoMigrationSourceAsset).status =
        AssetStatus.active) ∧
      ((demoMigrationAccountRegistry.metadata
        (demoMigrationAssetRegistry.metadata demoMigrationSourceAsset).issuer).status =
          AccountStatus.active)) ∧
    (((demoMigrationAssetRegistry.metadata demoMigrationDestinationAsset).status =
        AssetStatus.active) ∧
      ((demoMigrationAccountRegistry.metadata
        (demoMigrationAssetRegistry.metadata demoMigrationDestinationAsset).issuer).status =
          AccountStatus.active))
  constructor
  · constructor <;> rfl
  · constructor <;> rfl



/-! ## Authorized atomic cross-network migration regressions -/

def demoAuthorizedMigrationPartition :
    AuthorizedAssetMigrationPartition demoMigrationAssetRegistry where
  route := demoCrossNetworkMigrationRoute
  sourceHolder := typedDemoTreasury
  recipient := typedDemoCustomer
  source_holder_on_source_network := by
    simp [demoMigrationAssetRegistry, demoMigrationSourceAsset,
      demoMigrationSourceMetadata, typedDemoAssetMetadata,
      demoMigrationAccountRegistry, typedDemoTreasury, typedDemoNetwork,
      demoCrossNetworkMigrationRoute]
  recipient_on_destination_network := by
    simp [demoMigrationAssetRegistry, demoMigrationDestinationAsset,
      demoMigrationDestinationMetadata, demoMigrationAccountRegistry,
      typedDemoTreasury, typedDemoCustomer, demoMigrationOtherNetwork,
      demoCrossNetworkMigrationRoute]

def demoAuthorizedMigrationHolderLedgerMap :
    HolderLedgerMap (AccountId 2) (Option (AccountId 2)) where
  ledgerAccount := some
  injective_ledgerAccount := by
    intro left right h
    injection h

def demoAuthorizedMigrationInitialHoldings :
    HoldingsState (AccountId 2) (AssetId 2) :=
  issueToHolder (emptyHoldingsState (AccountId 2) (AssetId 2))
    typedDemoTreasury demoMigrationSourceAsset 2

def demoAuthorizedMigrationInitialLedger :
    Ledger (Option (AccountId 2)) (AssetId 2) :=
  ⟨fun ledgerAccount asset =>
    if ledgerAccount = some typedDemoTreasury ∧
        asset = demoMigrationSourceAsset then 2 else 0⟩

def demoAuthorizedMigrationInitialFinancial :
    FinancialState (AccountId 2) (Option (AccountId 2)) (AssetId 2) :=
  { holdings := demoAuthorizedMigrationInitialHoldings
    ledger := demoAuthorizedMigrationInitialLedger }

theorem demoAuthorizedMigrationInitialFinancial_invariant :
    FinancialInvariant demoAuthorizedMigrationHolderLedgerMap
      demoAuthorizedMigrationInitialFinancial := by
  constructor
  · exact issueToHolder_preserves_invariant
      (emptyHoldingsState (AccountId 2) (AssetId 2))
      (emptyHoldingsState_invariant)
      typedDemoTreasury demoMigrationSourceAsset 2
  · intro holder asset
    rcases holder with ⟨holderIndex⟩
    rcases asset with ⟨assetIndex⟩
    fin_cases holderIndex <;> fin_cases assetIndex <;>
      simp [demoAuthorizedMigrationInitialFinancial,
        demoAuthorizedMigrationInitialHoldings,
        demoAuthorizedMigrationInitialLedger,
        demoAuthorizedMigrationHolderLedgerMap,
        demoMigrationSourceAsset, typedDemoTreasury,
        issueToHolder, emptyHoldingsState]

def demoAuthorizedMigrationBurnGrant :
    AuthorityGrant DemoPrincipal (AccountId 2) (AssetId 2) :=
  { principal := .treasury
    scope := .burn typedDemoTreasury
    asset := demoMigrationSourceAsset
    maxAmount := 2 }

def demoAuthorizedMigrationIssueGrant :
    AuthorityGrant DemoPrincipal (AccountId 2) (AssetId 2) :=
  { principal := .treasury
    scope := .issue typedDemoCustomer typedDemoCustomer
    asset := demoMigrationDestinationAsset
    maxAmount := 1 }

def demoAuthorizedMigrationAuthority :
    AuthorityRegistry DemoPrincipal (AccountId 2) (AssetId 2) where
  grants := [demoAuthorizedMigrationBurnGrant, demoAuthorizedMigrationIssueGrant]
  unique_scope := by
    intro left right hLeftMem hRightMem _hPrincipal hScope _hAsset
    rcases List.mem_cons.mp hLeftMem with hLeftBurn | hLeftTail
    · cases hLeftBurn
      rcases List.mem_cons.mp hRightMem with hRightBurn | hRightTail
      · cases hRightBurn
        rfl
      · have hRightIssue : right = demoAuthorizedMigrationIssueGrant := by
          simpa using hRightTail
        cases hRightIssue
        cases hScope
    · have hLeftIssue : left = demoAuthorizedMigrationIssueGrant := by
        simpa using hLeftTail
      cases hLeftIssue
      rcases List.mem_cons.mp hRightMem with hRightBurn | hRightTail
      · cases hRightBurn
        cases hScope
      · have hRightIssue : right = demoAuthorizedMigrationIssueGrant := by
          simpa using hRightTail
        cases hRightIssue
        rfl


def demoAuthorizedMigrationControl :
    AccountControlRegistry DemoPrincipal (AccountId 2) where
  entries := [
    (DemoPrincipal.treasury, typedDemoTreasury),
    (DemoPrincipal.treasury, typedDemoCustomer)
  ]

theorem demoAuthorizedMigrationBurnAllowed
    (holdings : HoldingsState (AccountId 2) (AssetId 2)) :
    (toControlledAuthorizationPolicy demoAuthorizedMigrationControl
      demoAuthorizedMigrationAuthority).mayBurn holdings
        DemoPrincipal.treasury typedDemoTreasury demoMigrationSourceAsset 1 := by
  change AccountControlRegistry.controls demoAuthorizedMigrationControl
      DemoPrincipal.treasury typedDemoTreasury ∧
    AuthorityRegistry.allows demoAuthorizedMigrationAuthority
      DemoPrincipal.treasury (.burn typedDemoTreasury)
      demoMigrationSourceAsset 1
  constructor
  · simp [AccountControlRegistry.controls, demoAuthorizedMigrationControl]
  · exact ⟨demoAuthorizedMigrationBurnGrant,
      by simp [demoAuthorizedMigrationAuthority], rfl, rfl, rfl, by decide⟩

theorem demoAuthorizedMigrationIssueAllowed
    (holdings : HoldingsState (AccountId 2) (AssetId 2))
    (amount : Nat) (hAmount : amount ≤ 1) :
    (toControlledAuthorizationPolicy demoAuthorizedMigrationControl
      demoAuthorizedMigrationAuthority).mayIssue holdings
        DemoPrincipal.treasury typedDemoCustomer typedDemoCustomer
        demoMigrationDestinationAsset amount := by
  change AccountControlRegistry.controls demoAuthorizedMigrationControl
      DemoPrincipal.treasury typedDemoCustomer ∧
    AuthorityRegistry.allows demoAuthorizedMigrationAuthority
      DemoPrincipal.treasury
      (.issue typedDemoCustomer typedDemoCustomer)
      demoMigrationDestinationAsset amount
  constructor
  · simp [AccountControlRegistry.controls, demoAuthorizedMigrationControl]
  · exact ⟨demoAuthorizedMigrationIssueGrant,
      by simp [demoAuthorizedMigrationAuthority], rfl, rfl, rfl, hAmount⟩

theorem demoAuthorizedMigrationCounterpart_unmapped :
    ∀ holder : AccountId 2,
      (none : Option (AccountId 2)) ≠
        demoAuthorizedMigrationHolderLedgerMap.ledgerAccount holder := by
  intro holder
  simp [demoAuthorizedMigrationHolderLedgerMap]

def demoAuthorizedMigrationInitialState :
    AuthorizedAssetMigrationState demoAuthorizedMigrationPartition
      (Option (AccountId 2)) :=
  initialAuthorizedAssetMigrationState demoAuthorizedMigrationPartition
    demoAuthorizedMigrationInitialFinancial

def demoAuthorizedMigrationAfterFirst :
    AuthorizedAssetMigrationState demoAuthorizedMigrationPartition
      (Option (AccountId 2)) :=
  applyAuthorizedAssetMigration demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationPartition
    demoAuthorizedMigrationInitialState 1

def demoAuthorizedMigrationAfterSecond :
    AuthorizedAssetMigrationState demoAuthorizedMigrationPartition
      (Option (AccountId 2)) :=
  applyAuthorizedAssetMigration demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationPartition
    demoAuthorizedMigrationAfterFirst 1

theorem demoAuthorizedMigration_route_is_enabled :
    demoAuthorizedMigrationPartition.route.endpointsEnabled :=
  migration_demo_route_requires_active_endpoints

theorem demoAuthorizedMigration_source_holder_is_active :
    AccountRegistry.isActive demoMigrationAccountRegistry typedDemoTreasury := by
  simp [AccountRegistry.isActive, demoMigrationAccountRegistry,
    typedDemoTreasury]

theorem demoAuthorizedMigration_recipient_is_active :
    AccountRegistry.isActive demoMigrationAccountRegistry typedDemoCustomer := by
  simp [AccountRegistry.isActive, demoMigrationAccountRegistry,
    typedDemoTreasury, typedDemoCustomer]

theorem demoAuthorizedMigration_first_step :
    AuthorizedAssetMigrationStep demoAuthorizedMigrationControl
      demoAuthorizedMigrationAuthority demoAuthorizedMigrationHolderLedgerMap
      (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
      demoAuthorizedMigrationPartition DemoPrincipal.treasury 1
      demoAuthorizedMigrationInitialState demoAuthorizedMigrationAfterFirst := by
  have hReleased :
      demoAuthorizedMigrationInitialState.dust.targetBaseUnitsReleased 1 = 0 := by
    norm_num [demoAuthorizedMigrationInitialState,
      initialAuthorizedAssetMigrationState,
      AssetMigrationDustState.targetBaseUnitsReleased,
      AssetMigrationDustState.empty, AssetMigrationDustState.addSource,
      demoAssetMigrationRate, demoAuthorizedMigrationPartition,
      demoCrossNetworkMigrationRoute]
  have hIssue :
      (toControlledAuthorizationPolicy demoAuthorizedMigrationControl
        demoAuthorizedMigrationAuthority).mayIssue
          demoAuthorizedMigrationInitialState.financial.holdings
          DemoPrincipal.treasury
          (demoMigrationAssetRegistry.metadata
            demoAuthorizedMigrationPartition.route.destinationAsset).issuer
          demoAuthorizedMigrationPartition.recipient
          demoAuthorizedMigrationPartition.route.destinationAsset 0 := by
    simpa [demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute,
      demoMigrationAssetRegistry, demoMigrationDestinationAsset,
      demoMigrationDestinationMetadata, typedDemoCustomer] using
      (demoAuthorizedMigrationIssueAllowed
        demoAuthorizedMigrationInitialState.financial.holdings 0 (by decide))
  have hEnough :
      (1 : Int) ≤ demoAuthorizedMigrationInitialState.financial.holdings.balance
        demoAuthorizedMigrationPartition.sourceHolder
        demoAuthorizedMigrationPartition.route.sourceAsset := by
    norm_num [demoAuthorizedMigrationInitialState,
      initialAuthorizedAssetMigrationState,
      demoAuthorizedMigrationInitialFinancial,
      demoAuthorizedMigrationInitialHoldings,
      demoMigrationSourceAsset, typedDemoTreasury,
      issueToHolder, emptyHoldingsState,
      demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute]
  refine ⟨by decide,
    demoAuthorizedMigration_source_holder_is_active,
    demoAuthorizedMigration_recipient_is_active,
    demoAuthorizedMigration_route_is_enabled,
    demoAuthorizedMigrationBurnAllowed _,
    ?_, hEnough, rfl⟩
  simpa [hReleased] using hIssue

theorem demoAuthorizedMigration_second_step :
    AuthorizedAssetMigrationStep demoAuthorizedMigrationControl
      demoAuthorizedMigrationAuthority demoAuthorizedMigrationHolderLedgerMap
      (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
      demoAuthorizedMigrationPartition DemoPrincipal.treasury 1
      demoAuthorizedMigrationAfterFirst demoAuthorizedMigrationAfterSecond := by
  have hReleased :
      demoAuthorizedMigrationAfterFirst.dust.targetBaseUnitsReleased 1 = 1 := by
    norm_num [demoAuthorizedMigrationAfterFirst, applyAuthorizedAssetMigration,
      demoAuthorizedMigrationInitialState, initialAuthorizedAssetMigrationState,
      AssetMigrationDustState.targetBaseUnitsReleased,
      AssetMigrationDustState.empty, AssetMigrationDustState.addSource,
      demoAuthorizedMigrationInitialFinancial,
      demoAuthorizedMigrationInitialHoldings, demoMigrationSourceAsset,
      typedDemoTreasury, demoAssetMigrationRate, issueToHolder,
      burnFromHolder, emptyHoldingsState,
      demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute]
  have hIssue :
      (toControlledAuthorizationPolicy demoAuthorizedMigrationControl
        demoAuthorizedMigrationAuthority).mayIssue
          demoAuthorizedMigrationAfterFirst.financial.holdings
          DemoPrincipal.treasury
          (demoMigrationAssetRegistry.metadata
            demoAuthorizedMigrationPartition.route.destinationAsset).issuer
          demoAuthorizedMigrationPartition.recipient
          demoAuthorizedMigrationPartition.route.destinationAsset 1 := by
    simpa [demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute,
      demoMigrationAssetRegistry, demoMigrationDestinationAsset,
      demoMigrationDestinationMetadata, typedDemoCustomer] using
      (demoAuthorizedMigrationIssueAllowed
        demoAuthorizedMigrationAfterFirst.financial.holdings 1 (by decide))
  have hEnough :
      (1 : Int) ≤ demoAuthorizedMigrationAfterFirst.financial.holdings.balance
        demoAuthorizedMigrationPartition.sourceHolder
        demoAuthorizedMigrationPartition.route.sourceAsset := by
    norm_num [demoAuthorizedMigrationAfterFirst, applyAuthorizedAssetMigration,
      demoAuthorizedMigrationInitialState, initialAuthorizedAssetMigrationState,
      demoAuthorizedMigrationInitialFinancial, demoAuthorizedMigrationInitialHoldings,
      demoMigrationSourceAsset, demoMigrationDestinationAsset,
      typedDemoTreasury, typedDemoCustomer, demoAssetMigrationRate,
      issueToHolder, burnFromHolder, emptyHoldingsState,
      AssetMigrationDustState.addSource,
      AssetMigrationDustState.targetBaseUnitsReleased,
      demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute]
  refine ⟨by decide,
    demoAuthorizedMigration_source_holder_is_active,
    demoAuthorizedMigration_recipient_is_active,
    demoAuthorizedMigration_route_is_enabled,
    demoAuthorizedMigrationBurnAllowed _,
    ?_, hEnough, rfl⟩
  simpa [hReleased] using hIssue

def demoAuthorizedMigrationMachine :
    VerifiedStateMachine
      (AuthorizedAssetMigrationState demoAuthorizedMigrationPartition
        (Option (AccountId 2))) :=
  authorizedAssetMigrationMachine demoAuthorizedMigrationControl
    demoAuthorizedMigrationAuthority demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
    demoAuthorizedMigrationPartition demoAuthorizedMigrationInitialFinancial
    demoAuthorizedMigrationInitialFinancial_invariant

theorem demoAuthorizedMigration_initial_reachable :
    Reachable demoAuthorizedMigrationMachine demoAuthorizedMigrationInitialState :=
  Reachable.initial rfl

theorem demoAuthorizedMigration_after_first_reachable :
    Reachable demoAuthorizedMigrationMachine demoAuthorizedMigrationAfterFirst :=
  Reachable.step demoAuthorizedMigration_initial_reachable
    ⟨DemoPrincipal.treasury, 1, demoAuthorizedMigration_first_step⟩

theorem demoAuthorizedMigration_after_second_reachable :
    Reachable demoAuthorizedMigrationMachine demoAuthorizedMigrationAfterSecond :=
  Reachable.step demoAuthorizedMigration_after_first_reachable
    ⟨DemoPrincipal.treasury, 1, demoAuthorizedMigration_second_step⟩

theorem demoAuthorizedMigration_two_step_result :
    demoAuthorizedMigrationAfterSecond.financial.holdings.balance
        typedDemoTreasury demoMigrationSourceAsset = 0 ∧
    demoAuthorizedMigrationAfterSecond.financial.holdings.balance
        typedDemoCustomer demoMigrationDestinationAsset = 1 ∧
    demoAuthorizedMigrationAfterSecond.dust.totalSourceBaseUnits = 2 ∧
    demoAuthorizedMigrationAfterSecond.dust.totalTargetBaseUnits = 1 ∧
    demoAuthorizedMigrationAfterSecond.dust.dustNumerator = 1 := by
  norm_num [demoAuthorizedMigrationAfterSecond, applyAuthorizedAssetMigration,
    demoAuthorizedMigrationAfterFirst, demoAuthorizedMigrationInitialState,
    initialAuthorizedAssetMigrationState, demoAuthorizedMigrationInitialFinancial,
    demoAuthorizedMigrationInitialHoldings, demoMigrationSourceAsset,
    demoMigrationDestinationAsset, typedDemoTreasury, typedDemoCustomer,
    demoAssetMigrationRate, issueToHolder, burnFromHolder, emptyHoldingsState,
    AssetMigrationDustState.empty,
    AssetMigrationDustState.addSource,
    AssetMigrationDustState.targetBaseUnitsReleased,
    demoAuthorizedMigrationPartition, demoCrossNetworkMigrationRoute]

theorem demoAuthorizedMigration_preserves_complete_invariant :
    AuthorizedAssetMigrationInvariant demoAuthorizedMigrationHolderLedgerMap
      demoAuthorizedMigrationInitialFinancial.ledger
      demoAuthorizedMigrationAfterSecond :=
  authorizedAssetMigrationInvariant_of_reachable
    demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
    demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
    demoAuthorizedMigrationPartition demoAuthorizedMigrationInitialFinancial
    demoAuthorizedMigrationInitialFinancial_invariant
    demoAuthorizedMigration_after_second_reachable


/-! ## Per-principal nonce and replay-protection regressions -/

def demoReplayProtectedInitialState :
    ReplayProtectedAuthorizedAssetMigrationState DemoPrincipal
      demoAuthorizedMigrationPartition (Option (AccountId 2)) :=
  initialReplayProtectedAuthorizedAssetMigrationState DemoPrincipal
    demoAuthorizedMigrationPartition demoAuthorizedMigrationInitialFinancial

def demoReplayProtectedAfterFirst :
    ReplayProtectedAuthorizedAssetMigrationState DemoPrincipal
      demoAuthorizedMigrationPartition (Option (AccountId 2)) :=
  applyReplayProtectedAuthorizedAssetMigration DemoPrincipal
    demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationPartition
    demoReplayProtectedInitialState DemoPrincipal.treasury 0 1

def demoReplayProtectedAfterSecond :
    ReplayProtectedAuthorizedAssetMigrationState DemoPrincipal
      demoAuthorizedMigrationPartition (Option (AccountId 2)) :=
  applyReplayProtectedAuthorizedAssetMigration DemoPrincipal
    demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationPartition
    demoReplayProtectedAfterFirst DemoPrincipal.treasury 1 1

theorem demoReplayProtected_first_step :
    ReplayProtectedAuthorizedAssetMigrationStep DemoPrincipal
      demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
      demoAuthorizedMigrationHolderLedgerMap
      (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
      demoAuthorizedMigrationPartition DemoPrincipal.treasury 0 1
      demoReplayProtectedInitialState demoReplayProtectedAfterFirst := by
  refine ⟨by rfl, ?_, rfl⟩
  exact demoAuthorizedMigration_first_step

theorem demoReplayProtected_first_nonce_advances :
    demoReplayProtectedAfterFirst.nextNonce DemoPrincipal.treasury = 1 := by
  simpa using
    (replayProtectedAuthorizedAssetMigrationStep_next_nonce
      DemoPrincipal demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
      demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
      demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
      DemoPrincipal.treasury 0 1 demoReplayProtected_first_step)

theorem demoReplayProtected_other_principal_nonce_is_unchanged :
    demoReplayProtectedAfterFirst.nextNonce DemoPrincipal.auditor = 0 := by
  simpa [demoReplayProtectedInitialState,
    initialReplayProtectedAuthorizedAssetMigrationState] using
    (replayProtectedAuthorizedAssetMigrationStep_other_nonce
      DemoPrincipal demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
      demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
      demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
      DemoPrincipal.treasury DemoPrincipal.auditor 0 1 demoReplayProtected_first_step
      (by decide))

theorem demoReplayProtected_stale_nonce_zero_rejected :
    ∀ after,
      ¬ ReplayProtectedAuthorizedAssetMigrationStep DemoPrincipal
        demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
        demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
        demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
        DemoPrincipal.treasury 0 1 demoReplayProtectedAfterFirst after := by
  intro after
  apply replayProtectedAuthorizedAssetMigrationStep_reject_nonce_mismatch
  rw [demoReplayProtected_first_nonce_advances]
  decide

theorem demoReplayProtected_future_nonce_two_rejected :
    ∀ after,
      ¬ ReplayProtectedAuthorizedAssetMigrationStep DemoPrincipal
        demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
        demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
        demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
        DemoPrincipal.treasury 2 1 demoReplayProtectedAfterFirst after := by
  intro after
  apply replayProtectedAuthorizedAssetMigrationStep_reject_nonce_mismatch
  rw [demoReplayProtected_first_nonce_advances]
  decide

theorem demoReplayProtected_second_step :
    ReplayProtectedAuthorizedAssetMigrationStep DemoPrincipal
      demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
      demoAuthorizedMigrationHolderLedgerMap
      (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
      demoAuthorizedMigrationPartition DemoPrincipal.treasury 1 1
      demoReplayProtectedAfterFirst demoReplayProtectedAfterSecond := by
  refine ⟨?_, demoAuthorizedMigration_second_step, rfl⟩
  simpa using demoReplayProtected_first_nonce_advances.symm

def demoReplayProtectedMachine :
    VerifiedStateMachine
      (ReplayProtectedAuthorizedAssetMigrationState DemoPrincipal
        demoAuthorizedMigrationPartition (Option (AccountId 2))) :=
  replayProtectedAuthorizedAssetMigrationMachine DemoPrincipal
    demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
    demoAuthorizedMigrationHolderLedgerMap
    (none : Option (AccountId 2)) demoAuthorizedMigrationCounterpart_unmapped
    demoAuthorizedMigrationPartition demoAuthorizedMigrationInitialFinancial
    demoAuthorizedMigrationInitialFinancial_invariant

theorem demoReplayProtected_initial_reachable :
    Reachable demoReplayProtectedMachine demoReplayProtectedInitialState :=
  Reachable.initial rfl

theorem demoReplayProtected_after_first_reachable :
    Reachable demoReplayProtectedMachine demoReplayProtectedAfterFirst :=
  Reachable.step demoReplayProtected_initial_reachable
    ⟨DemoPrincipal.treasury, 0, 1, demoReplayProtected_first_step⟩

theorem demoReplayProtected_after_second_reachable :
    Reachable demoReplayProtectedMachine demoReplayProtectedAfterSecond :=
  Reachable.step demoReplayProtected_after_first_reachable
    ⟨DemoPrincipal.treasury, 1, 1, demoReplayProtected_second_step⟩

theorem demoReplayProtected_two_step_result :
    demoReplayProtectedAfterSecond.migration.financial.holdings.balance
        typedDemoTreasury demoMigrationSourceAsset = 0 ∧
    demoReplayProtectedAfterSecond.migration.financial.holdings.balance
        typedDemoCustomer demoMigrationDestinationAsset = 1 ∧
    demoReplayProtectedAfterSecond.migration.dust.totalSourceBaseUnits = 2 ∧
    demoReplayProtectedAfterSecond.migration.dust.totalTargetBaseUnits = 1 ∧
    demoReplayProtectedAfterSecond.migration.dust.dustNumerator = 1 ∧
    demoReplayProtectedAfterSecond.nextNonce DemoPrincipal.treasury = 2 ∧
    demoReplayProtectedAfterSecond.nextNonce DemoPrincipal.auditor = 0 := by
  have hMigration :
      demoReplayProtectedAfterSecond.migration = demoAuthorizedMigrationAfterSecond := rfl
  rcases demoAuthorizedMigration_two_step_result with
    ⟨hSource, hDestination, hTotalSource, hTotalTarget, hDust⟩
  have hTreasuryNonce :
      demoReplayProtectedAfterSecond.nextNonce DemoPrincipal.treasury = 2 := by
    simpa using
      (replayProtectedAuthorizedAssetMigrationStep_next_nonce
        DemoPrincipal demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
        demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
        demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
        DemoPrincipal.treasury 1 1 demoReplayProtected_second_step)
  have hAuditorNonce :
      demoReplayProtectedAfterSecond.nextNonce DemoPrincipal.auditor = 0 := by
    calc
      demoReplayProtectedAfterSecond.nextNonce DemoPrincipal.auditor =
          demoReplayProtectedAfterFirst.nextNonce DemoPrincipal.auditor :=
        replayProtectedAuthorizedAssetMigrationStep_other_nonce
          DemoPrincipal demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
          demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
          demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
          DemoPrincipal.treasury DemoPrincipal.auditor 1 1
          demoReplayProtected_second_step (by decide)
      _ = 0 := demoReplayProtected_other_principal_nonce_is_unchanged
  rw [hMigration]
  exact ⟨hSource, hDestination, hTotalSource, hTotalTarget, hDust,
    hTreasuryNonce, hAuditorNonce⟩

theorem demoReplayProtected_preserves_complete_invariant :
    ReplayProtectedAuthorizedAssetMigrationInvariant DemoPrincipal
      demoAuthorizedMigrationHolderLedgerMap demoAuthorizedMigrationInitialFinancial.ledger
      demoReplayProtectedAfterSecond :=
  replayProtectedAuthorizedAssetMigrationInvariant_of_reachable
    DemoPrincipal demoAuthorizedMigrationControl demoAuthorizedMigrationAuthority
    demoAuthorizedMigrationHolderLedgerMap (none : Option (AccountId 2))
    demoAuthorizedMigrationCounterpart_unmapped demoAuthorizedMigrationPartition
    demoAuthorizedMigrationInitialFinancial demoAuthorizedMigrationInitialFinancial_invariant
    demoReplayProtected_after_second_reachable



/-! ## Exact fee-accounting arithmetic regressions -/

theorem feeAccounting_gross_splits_into_net_and_fee :
    feeTransferNetAmount 1000 25 + 25 = 1000 := by
  norm_num [feeTransferNetAmount]

theorem feeAccounting_zero_fee_preserves_gross_amount :
    feeTransferNetAmount 1000 0 = 1000 := by
  rfl

theorem feeAccounting_full_fee_leaves_zero_net :
    feeTransferNetAmount 1000 1000 = 0 := by
  rfl

theorem feeAccounting_fee_above_gross_is_not_admissible :
    ¬ 1001 ≤ 1000 := by
  decide

theorem feeAccounting_net_and_fee_are_exact_for_any_admissible_fee
    (gross fee : Nat) (hFee : fee ≤ gross) :
    feeTransferNetAmount gross fee + fee = gross :=
  feeTransferNetAmount_add_fee gross fee hFee

/-! ## Authorized escrow accounting regressions -/

inductive EscrowDemoHolder
  | alice
  | bob
  | vault
  | treasury
  deriving DecidableEq, Repr

instance : Fintype EscrowDemoHolder :=
  Fintype.ofList
    [EscrowDemoHolder.alice, EscrowDemoHolder.bob,
      EscrowDemoHolder.vault, EscrowDemoHolder.treasury] (by
    intro holder
    cases holder <;> simp)

@[simp] theorem escrowDemo_alice_ne_bob :
    EscrowDemoHolder.alice ≠ EscrowDemoHolder.bob := by decide

@[simp] theorem escrowDemo_bob_ne_alice :
    EscrowDemoHolder.bob ≠ EscrowDemoHolder.alice := by decide

@[simp] theorem escrowDemo_alice_ne_vault :
    EscrowDemoHolder.alice ≠ EscrowDemoHolder.vault := by decide

@[simp] theorem escrowDemo_vault_ne_alice :
    EscrowDemoHolder.vault ≠ EscrowDemoHolder.alice := by decide

@[simp] theorem escrowDemo_bob_ne_vault :
    EscrowDemoHolder.bob ≠ EscrowDemoHolder.vault := by decide

@[simp] theorem escrowDemo_vault_ne_bob :
    EscrowDemoHolder.vault ≠ EscrowDemoHolder.bob := by decide

inductive EscrowDemoAsset
  | rft
  deriving DecidableEq, Repr

instance : Fintype EscrowDemoAsset :=
  Fintype.ofList [EscrowDemoAsset.rft] (by
    intro asset
    cases asset <;> simp)

inductive EscrowDemoPrincipal
  | aliceOperator
  | escrowAgent
  deriving DecidableEq, Repr

def escrowDemoMapping :
    HolderLedgerMap EscrowDemoHolder EscrowDemoHolder :=
  { ledgerAccount := fun holder => holder
    injective_ledgerAccount := by
      intro left right h
      exact h }

def escrowDemoInitialHoldings :
    HoldingsState EscrowDemoHolder EscrowDemoAsset :=
  issueToHolder
    (emptyHoldingsState EscrowDemoHolder EscrowDemoAsset)
    EscrowDemoHolder.alice EscrowDemoAsset.rft 100

theorem escrowDemoInitialHoldings_invariant :
    HoldingsInvariant escrowDemoInitialHoldings := by
  exact issueToHolder_preserves_invariant
    (emptyHoldingsState EscrowDemoHolder EscrowDemoAsset)
    emptyHoldingsState_invariant
    EscrowDemoHolder.alice EscrowDemoAsset.rft 100

def escrowDemoOpeningLedger :
    Ledger EscrowDemoHolder EscrowDemoAsset :=
  ⟨fun holder asset => escrowDemoInitialHoldings.balance holder asset⟩

/-- The opening GL is the identity image of the initial holdings ledger. -/
@[simp] theorem escrowDemoOpeningLedger_alice_balance :
    escrowDemoOpeningLedger.balance EscrowDemoHolder.alice EscrowDemoAsset.rft = 100 := by
  norm_num [escrowDemoOpeningLedger, escrowDemoInitialHoldings,
    issueToHolder, emptyHoldingsState]

@[simp] theorem escrowDemoOpeningLedger_bob_balance :
    escrowDemoOpeningLedger.balance EscrowDemoHolder.bob EscrowDemoAsset.rft = 0 := by
  norm_num [escrowDemoOpeningLedger, escrowDemoInitialHoldings,
    issueToHolder, emptyHoldingsState]

@[simp] theorem escrowDemoOpeningLedger_vault_balance :
    escrowDemoOpeningLedger.balance EscrowDemoHolder.vault EscrowDemoAsset.rft = 0 := by
  norm_num [escrowDemoOpeningLedger, escrowDemoInitialHoldings,
    issueToHolder, emptyHoldingsState]

def escrowDemoInitialFinancial :
    FinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  { holdings := escrowDemoInitialHoldings
    ledger := escrowDemoOpeningLedger }

theorem escrowDemoInitialFinancial_conservation :
    FinancialConservationInvariant escrowDemoMapping
      escrowDemoOpeningLedger escrowDemoInitialFinancial := by
  refine ⟨?_, ?_⟩
  · exact ⟨escrowDemoInitialHoldings_invariant, by
      intro holder asset
      rfl⟩
  · intro asset
    rfl

def escrowDemoInitialRecord :
    EscrowRecord EscrowDemoHolder EscrowDemoAsset :=
  { depositor := EscrowDemoHolder.alice
    beneficiary := EscrowDemoHolder.bob
    asset := EscrowDemoAsset.rft
    amount := 0
    phase := EscrowPhase.ready }

def escrowDemoInitialState :
    EscrowFinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  { financial := escrowDemoInitialFinancial
    record := escrowDemoInitialRecord }

theorem escrowDemoInitial_invariant :
    EscrowFinancialInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault escrowDemoInitialState := by
  refine ⟨escrowDemoInitialFinancial_conservation, ?_, ?_⟩
  · intro asset
    cases asset
    simp [escrowDemoInitialState, escrowDemoInitialRecord,
      escrowDemoInitialFinancial, escrowDemoInitialHoldings,
      emptyHoldingsState, issueToHolder]
  · intro hPending
    cases hPending

def escrowDemoTransferPolicy :
    AuthorizationPolicy EscrowDemoPrincipal EscrowDemoHolder EscrowDemoAsset where
  mayTransfer := fun _ principal source destination asset amount =>
    (principal = EscrowDemoPrincipal.aliceOperator ∧
      source = EscrowDemoHolder.alice ∧
      destination = EscrowDemoHolder.vault ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40) ∨
    (principal = EscrowDemoPrincipal.escrowAgent ∧
      source = EscrowDemoHolder.vault ∧
      destination = EscrowDemoHolder.bob ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40) ∨
    (principal = EscrowDemoPrincipal.escrowAgent ∧
      source = EscrowDemoHolder.vault ∧
      destination = EscrowDemoHolder.alice ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40)
  mayIssue := fun _ _ _ _ _ _ => False
  mayBurn := fun _ _ _ _ _ => False

def escrowDemoEscrowPolicy :
    EscrowAuthorizationPolicy EscrowDemoPrincipal EscrowDemoHolder EscrowDemoAsset where
  mayOpenEscrow := fun _ principal depositor beneficiary escrowVault asset amount =>
    principal = EscrowDemoPrincipal.aliceOperator ∧
      depositor = EscrowDemoHolder.alice ∧
      beneficiary = EscrowDemoHolder.bob ∧
      escrowVault = EscrowDemoHolder.vault ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40
  mayReleaseEscrow := fun _ principal escrowVault depositor beneficiary asset amount =>
    principal = EscrowDemoPrincipal.escrowAgent ∧
      escrowVault = EscrowDemoHolder.vault ∧
      depositor = EscrowDemoHolder.alice ∧
      beneficiary = EscrowDemoHolder.bob ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40
  mayCancelEscrow := fun _ principal escrowVault depositor beneficiary asset amount =>
    principal = EscrowDemoPrincipal.escrowAgent ∧
      escrowVault = EscrowDemoHolder.vault ∧
      depositor = EscrowDemoHolder.alice ∧
      beneficiary = EscrowDemoHolder.bob ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40

def escrowDemoDenyAllEscrowPolicy :
    EscrowAuthorizationPolicy EscrowDemoPrincipal EscrowDemoHolder EscrowDemoAsset where
  mayOpenEscrow := fun _ _ _ _ _ _ _ => False
  mayReleaseEscrow := fun _ _ _ _ _ _ _ => False
  mayCancelEscrow := fun _ _ _ _ _ _ _ => False

theorem escrowDemo_open_transfer_authorized :
    escrowDemoTransferPolicy.mayTransfer escrowDemoInitialHoldings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.vault EscrowDemoAsset.rft 40 := by
  simp [escrowDemoTransferPolicy]

theorem escrowDemo_open_escrow_authorized :
    escrowDemoEscrowPolicy.mayOpenEscrow escrowDemoInitialHoldings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.bob EscrowDemoHolder.vault EscrowDemoAsset.rft 40 := by
  simp [escrowDemoEscrowPolicy]

theorem escrowDemo_open_funded :
    TransferAllowed escrowDemoInitialHoldings
      EscrowDemoHolder.alice EscrowDemoHolder.vault EscrowDemoAsset.rft 40 := by
  right
  norm_num [TransferAllowed, escrowDemoInitialHoldings,
    issueToHolder, emptyHoldingsState]

def escrowDemoAfterOpen :
    EscrowFinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  openEscrowFinancialState escrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault escrowDemoInitialState
    EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
    EscrowDemoHolder.bob EscrowDemoAsset.rft 40
    escrowDemo_open_transfer_authorized escrowDemo_open_funded

theorem escrowDemo_open_step :
    EscrowOpenStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
      escrowDemoMapping EscrowDemoHolder.vault
      escrowDemoInitialState escrowDemoAfterOpen := by
  refine ⟨EscrowDemoPrincipal.aliceOperator, EscrowDemoHolder.alice,
    EscrowDemoHolder.bob, EscrowDemoAsset.rft, 40,
    by decide, by decide, by decide, by decide,
    escrowDemo_open_transfer_authorized, escrowDemo_open_escrow_authorized,
    escrowDemo_open_funded, rfl⟩

theorem escrowDemo_open_denied_without_escrow_permission :
    ∀ after,
      ¬ EscrowOpenStep escrowDemoTransferPolicy escrowDemoDenyAllEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoInitialState after := by
  intro after hStep
  rcases hStep with
    ⟨principal, depositor, beneficiary, asset, amount, hReady,
      hNotDepositor, hNotBeneficiary, hPositive, hTransfer, hEscrow, hAllowed, hEq⟩
  simp [escrowDemoDenyAllEscrowPolicy] at hEscrow

theorem escrowDemo_release_transfer_authorized :
    escrowDemoTransferPolicy.mayTransfer escrowDemoAfterOpen.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  simp [escrowDemoTransferPolicy]

theorem escrowDemo_release_escrow_authorized :
    escrowDemoEscrowPolicy.mayReleaseEscrow escrowDemoAfterOpen.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  simp [escrowDemoEscrowPolicy]

theorem escrowDemo_release_funded :
    TransferAllowed escrowDemoAfterOpen.financial.holdings
      EscrowDemoHolder.vault EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  right
  change (40 : Int) ≤
    escrowDemoAfterOpen.financial.holdings.balance
      EscrowDemoHolder.vault EscrowDemoAsset.rft
  norm_num [escrowDemoMapping, escrowDemoAfterOpen, openEscrowFinancialState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders,
    escrowDemoInitialState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState]

def escrowDemoAfterRelease :
    EscrowFinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  releaseEscrowFinancialState escrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault escrowDemoAfterOpen EscrowDemoPrincipal.escrowAgent
    escrowDemo_release_transfer_authorized escrowDemo_release_funded

theorem escrowDemo_release_step :
    EscrowReleaseStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
      escrowDemoMapping EscrowDemoHolder.vault
      escrowDemoAfterOpen escrowDemoAfterRelease := by
  refine ⟨EscrowDemoPrincipal.escrowAgent, rfl,
    escrowDemo_release_transfer_authorized, escrowDemo_release_escrow_authorized,
    escrowDemo_release_funded, rfl⟩

theorem escrowDemo_cancel_transfer_authorized :
    escrowDemoTransferPolicy.mayTransfer escrowDemoAfterOpen.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoAsset.rft 40 := by
  simp [escrowDemoTransferPolicy]

theorem escrowDemo_cancel_escrow_authorized :
    escrowDemoEscrowPolicy.mayCancelEscrow escrowDemoAfterOpen.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  simp [escrowDemoEscrowPolicy]

theorem escrowDemo_cancel_funded :
    TransferAllowed escrowDemoAfterOpen.financial.holdings
      EscrowDemoHolder.vault EscrowDemoHolder.alice EscrowDemoAsset.rft 40 := by
  right
  change (40 : Int) ≤
    escrowDemoAfterOpen.financial.holdings.balance
      EscrowDemoHolder.vault EscrowDemoAsset.rft
  norm_num [escrowDemoMapping, escrowDemoAfterOpen, openEscrowFinancialState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders,
    escrowDemoInitialState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState]

def escrowDemoAfterCancel :
    EscrowFinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  cancelEscrowFinancialState escrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault escrowDemoAfterOpen EscrowDemoPrincipal.escrowAgent
    escrowDemo_cancel_transfer_authorized escrowDemo_cancel_funded

theorem escrowDemo_cancel_step :
    EscrowCancelStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
      escrowDemoMapping EscrowDemoHolder.vault
      escrowDemoAfterOpen escrowDemoAfterCancel := by
  refine ⟨EscrowDemoPrincipal.escrowAgent, rfl,
    escrowDemo_cancel_transfer_authorized, escrowDemo_cancel_escrow_authorized,
    escrowDemo_cancel_funded, rfl⟩

def escrowDemoMachine :
    VerifiedStateMachine
      (EscrowFinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset) :=
  escrowFinancialMachine escrowDemoTransferPolicy escrowDemoEscrowPolicy
    escrowDemoMapping escrowDemoOpeningLedger EscrowDemoHolder.vault
    escrowDemoInitialState escrowDemoInitial_invariant

theorem escrowDemo_initial_reachable :
    Reachable escrowDemoMachine escrowDemoInitialState :=
  Reachable.initial rfl

theorem escrowDemo_after_open_reachable :
    Reachable escrowDemoMachine escrowDemoAfterOpen :=
  Reachable.step escrowDemo_initial_reachable (Or.inl escrowDemo_open_step)

theorem escrowDemo_after_release_reachable :
    Reachable escrowDemoMachine escrowDemoAfterRelease :=
  Reachable.step escrowDemo_after_open_reachable
    (Or.inr (Or.inl escrowDemo_release_step))

theorem escrowDemo_after_cancel_reachable :
    Reachable escrowDemoMachine escrowDemoAfterCancel :=
  Reachable.step escrowDemo_after_open_reachable
    (Or.inr (Or.inr escrowDemo_cancel_step))

theorem escrowDemo_after_release_invariant :
    EscrowFinancialInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault escrowDemoAfterRelease :=
  escrowFinancialInvariant_of_reachable escrowDemoTransferPolicy
    escrowDemoEscrowPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault escrowDemoInitialState escrowDemoInitial_invariant
    escrowDemo_after_release_reachable

theorem escrowDemo_after_cancel_invariant :
    EscrowFinancialInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault escrowDemoAfterCancel :=
  escrowFinancialInvariant_of_reachable escrowDemoTransferPolicy
    escrowDemoEscrowPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault escrowDemoInitialState escrowDemoInitial_invariant
    escrowDemo_after_cancel_reachable

theorem escrowDemo_open_exact_balances :
    escrowDemoAfterOpen.financial.holdings.balance EscrowDemoHolder.alice
        EscrowDemoAsset.rft = 60 ∧
    escrowDemoAfterOpen.financial.holdings.balance EscrowDemoHolder.vault
        EscrowDemoAsset.rft = 40 ∧
    escrowDemoAfterOpen.financial.holdings.balance EscrowDemoHolder.bob
        EscrowDemoAsset.rft = 0 ∧
    escrowDemoAfterOpen.financial.holdings.supply EscrowDemoAsset.rft =
      escrowDemoInitialHoldings.supply EscrowDemoAsset.rft ∧
    escrowDemoAfterOpen.financial.ledger.balance EscrowDemoHolder.vault
      EscrowDemoAsset.rft = 40 := by
  norm_num [escrowDemoMapping, escrowDemoAfterOpen, openEscrowFinancialState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders,
    escrowDemoInitialState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
    postJournal, holderTransferJournal, transferJournal]

theorem escrowDemo_release_exact_balances :
    escrowDemoAfterRelease.financial.holdings.balance EscrowDemoHolder.alice
        EscrowDemoAsset.rft = 60 ∧
    escrowDemoAfterRelease.financial.holdings.balance EscrowDemoHolder.vault
        EscrowDemoAsset.rft = 0 ∧
    escrowDemoAfterRelease.financial.holdings.balance EscrowDemoHolder.bob
        EscrowDemoAsset.rft = 40 ∧
    escrowDemoAfterRelease.financial.holdings.supply EscrowDemoAsset.rft =
      escrowDemoInitialHoldings.supply EscrowDemoAsset.rft ∧
    escrowDemoAfterRelease.financial.ledger.balance EscrowDemoHolder.bob
      EscrowDemoAsset.rft = 40 := by
  norm_num [escrowDemoMapping, escrowDemoAfterRelease, releaseEscrowFinancialState,
    escrowDemoAfterOpen, openEscrowFinancialState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders,
    escrowDemoInitialState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
    postJournal, holderTransferJournal, transferJournal]

theorem escrowDemo_cancel_exact_balances :
    escrowDemoAfterCancel.financial.holdings.balance EscrowDemoHolder.alice
        EscrowDemoAsset.rft = 100 ∧
    escrowDemoAfterCancel.financial.holdings.balance EscrowDemoHolder.vault
        EscrowDemoAsset.rft = 0 ∧
    escrowDemoAfterCancel.financial.holdings.balance EscrowDemoHolder.bob
        EscrowDemoAsset.rft = 0 ∧
    escrowDemoAfterCancel.financial.holdings.supply EscrowDemoAsset.rft =
      escrowDemoInitialHoldings.supply EscrowDemoAsset.rft ∧
    escrowDemoAfterCancel.financial.ledger.balance EscrowDemoHolder.alice
      EscrowDemoAsset.rft = 100 := by
  norm_num [escrowDemoMapping, escrowDemoAfterCancel, cancelEscrowFinancialState,
    escrowDemoAfterOpen, openEscrowFinancialState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders,
    escrowDemoInitialState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
    postJournal, holderTransferJournal, transferJournal]

theorem escrowDemo_open_cannot_repeat :
    ∀ after,
      ¬ EscrowOpenStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterOpen after := by
  intro after hStep
  rcases hStep with
    ⟨principal, depositor, beneficiary, asset, amount, hReady,
      hNotDepositor, hNotBeneficiary, hPositive, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.pending = EscrowPhase.ready := by
    simpa [escrowDemoAfterOpen, openEscrowFinancialState] using hReady
  cases hImpossible

theorem escrowDemo_release_cannot_repeat :
    ∀ after,
      ¬ EscrowReleaseStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterRelease after := by
  intro after hStep
  rcases hStep with ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.released = EscrowPhase.pending := by
    simpa [escrowDemoAfterRelease, releaseEscrowFinancialState] using hPending
  cases hImpossible

theorem escrowDemo_cancel_cannot_repeat :
    ∀ after,
      ¬ EscrowCancelStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterCancel after := by
  intro after hStep
  rcases hStep with ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.cancelled = EscrowPhase.pending := by
    simpa [escrowDemoAfterCancel, cancelEscrowFinancialState] using hPending
  cases hImpossible

theorem escrowDemo_release_after_cancel_is_denied :
    ∀ after,
      ¬ EscrowReleaseStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterCancel after := by
  intro after hStep
  rcases hStep with ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.cancelled = EscrowPhase.pending := by
    simpa [escrowDemoAfterCancel, cancelEscrowFinancialState] using hPending
  cases hImpossible


theorem escrowDemo_open_after_release_is_denied :
    ∀ after,
      ¬ EscrowOpenStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterRelease after := by
  intro after hStep
  rcases hStep with
    ⟨principal, depositor, beneficiary, asset, amount, hReady,
      hNotDepositor, hNotBeneficiary, hPositive, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.released = EscrowPhase.ready := by
    simpa [escrowDemoAfterRelease, releaseEscrowFinancialState,
      escrowDemoAfterOpen, openEscrowFinancialState] using hReady
  cases hImpossible

theorem escrowDemo_open_after_cancel_is_denied :
    ∀ after,
      ¬ EscrowOpenStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterCancel after := by
  intro after hStep
  rcases hStep with
    ⟨principal, depositor, beneficiary, asset, amount, hReady,
      hNotDepositor, hNotBeneficiary, hPositive, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.cancelled = EscrowPhase.ready := by
    simpa [escrowDemoAfterCancel, cancelEscrowFinancialState,
      escrowDemoAfterOpen, openEscrowFinancialState] using hReady
  cases hImpossible

theorem escrowDemo_cancel_after_release_is_denied :
    ∀ after,
      ¬ EscrowCancelStep escrowDemoTransferPolicy escrowDemoEscrowPolicy
        escrowDemoMapping EscrowDemoHolder.vault escrowDemoAfterRelease after := by
  intro after hStep
  rcases hStep with ⟨principal, hPending, hTransfer, hEscrow, hAllowed, hEq⟩
  have hImpossible : EscrowPhase.released = EscrowPhase.pending := by
    simpa [escrowDemoAfterRelease, releaseEscrowFinancialState] using hPending
  cases hImpossible
/-! ## Multi-escrow registry regressions -/

abbrev EscrowRegistryDemoId := Bool

def escrowRegistryDemoEmpty :
    EscrowRegistry EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  emptyEscrowRegistry

def escrowRegistryDemoAlphaRecord :
    EscrowRecord EscrowDemoHolder EscrowDemoAsset :=
  { depositor := EscrowDemoHolder.alice
    beneficiary := EscrowDemoHolder.bob
    asset := EscrowDemoAsset.rft
    amount := 40
    phase := EscrowPhase.pending }

def escrowRegistryDemoBetaRecord :
    EscrowRecord EscrowDemoHolder EscrowDemoAsset :=
  { depositor := EscrowDemoHolder.bob
    beneficiary := EscrowDemoHolder.alice
    asset := EscrowDemoAsset.rft
    amount := 25
    phase := EscrowPhase.pending }

theorem escrowRegistryDemoEmpty_invariant :
    EscrowRegistryInvariant escrowRegistryDemoEmpty := by
  intro id record hRecord
  simp [escrowRegistryDemoEmpty, emptyEscrowRegistry] at hRecord

def escrowRegistryDemoAfterAlpha :
    EscrowRegistry EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  escrowRegistryInsert escrowRegistryDemoEmpty false escrowRegistryDemoAlphaRecord

theorem escrowRegistryDemoAfterAlpha_invariant :
    EscrowRegistryInvariant escrowRegistryDemoAfterAlpha := by
  exact escrowRegistryInsert_preserves_invariant
    escrowRegistryDemoEmpty false escrowRegistryDemoAlphaRecord
    escrowRegistryDemoEmpty_invariant
    (by simp [escrowRegistryDemoEmpty, emptyEscrowRegistry])
    rfl
    (by decide)

theorem escrowRegistryDemo_beta_is_fresh_after_alpha :
    escrowRegistryDemoAfterAlpha.records true = none := by
  simp [escrowRegistryDemoAfterAlpha, escrowRegistryDemoEmpty,
    emptyEscrowRegistry, escrowRegistryInsert]

def escrowRegistryDemoAfterBoth :
    EscrowRegistry EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  escrowRegistryInsert escrowRegistryDemoAfterAlpha true escrowRegistryDemoBetaRecord

theorem escrowRegistryDemoAfterBoth_invariant :
    EscrowRegistryInvariant escrowRegistryDemoAfterBoth := by
  exact escrowRegistryInsert_preserves_invariant
    escrowRegistryDemoAfterAlpha true escrowRegistryDemoBetaRecord
    escrowRegistryDemoAfterAlpha_invariant
    escrowRegistryDemo_beta_is_fresh_after_alpha
    rfl
    (by decide)

@[simp] theorem escrowRegistryDemoAfterBoth_alpha :
    escrowRegistryDemoAfterBoth.records false =
      some escrowRegistryDemoAlphaRecord := by
  simp [escrowRegistryDemoAfterBoth, escrowRegistryDemoAfterAlpha,
    escrowRegistryDemoEmpty, emptyEscrowRegistry, escrowRegistryInsert]

@[simp] theorem escrowRegistryDemoAfterBoth_beta :
    escrowRegistryDemoAfterBoth.records true =
      some escrowRegistryDemoBetaRecord := by
  simp [escrowRegistryDemoAfterBoth, escrowRegistryDemoAfterAlpha,
    escrowRegistryDemoEmpty, emptyEscrowRegistry, escrowRegistryInsert]

def escrowRegistryDemoAfterReleaseAlpha :
    EscrowRegistry EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  escrowRegistryRelease escrowRegistryDemoAfterBoth false
    escrowRegistryDemoAlphaRecord

theorem escrowRegistryDemo_release_alpha_step :
    EscrowRegistryReleaseStep escrowRegistryDemoAfterBoth
      escrowRegistryDemoAfterReleaseAlpha := by
  exact ⟨false, escrowRegistryDemoAlphaRecord,
    escrowRegistryDemoAfterBoth_alpha, rfl, rfl⟩

theorem escrowRegistryDemoAfterReleaseAlpha_invariant :
    EscrowRegistryInvariant escrowRegistryDemoAfterReleaseAlpha := by
  exact escrowRegistryRelease_preserves_invariant
    escrowRegistryDemoAfterBoth false escrowRegistryDemoAlphaRecord
    escrowRegistryDemoAfterBoth_invariant
    escrowRegistryDemoAfterBoth_alpha rfl

@[simp] theorem escrowRegistryDemoAfterReleaseAlpha_alpha :
    escrowRegistryDemoAfterReleaseAlpha.records false =
      some { escrowRegistryDemoAlphaRecord with phase := EscrowPhase.released } := by
  simp [escrowRegistryDemoAfterReleaseAlpha, escrowRegistryRelease]

@[simp] theorem escrowRegistryDemoAfterReleaseAlpha_beta :
    escrowRegistryDemoAfterReleaseAlpha.records true =
      some escrowRegistryDemoBetaRecord := by
  simp [escrowRegistryDemoAfterReleaseAlpha, escrowRegistryDemoAfterBoth,
    escrowRegistryDemoAfterAlpha, escrowRegistryDemoEmpty,
    emptyEscrowRegistry, escrowRegistryRelease, escrowRegistryInsert]

theorem escrowRegistryDemo_alpha_id_not_free_after_release :
    escrowRegistryDemoAfterReleaseAlpha.records false ≠ none := by
  rw [escrowRegistryDemoAfterReleaseAlpha_alpha]
  simp

theorem escrowRegistryDemo_alpha_cannot_be_reopened :
    ¬ ∃ replacement : EscrowRecord EscrowDemoHolder EscrowDemoAsset,
      escrowRegistryDemoAfterReleaseAlpha.records false = none := by
  intro hFree
  rcases hFree with ⟨replacement, hNone⟩
  rw [escrowRegistryDemoAfterReleaseAlpha_alpha] at hNone
  cases hNone

def escrowRegistryDemoAfterCancelBeta :
    EscrowRegistry EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  escrowRegistryCancel escrowRegistryDemoAfterReleaseAlpha true
    escrowRegistryDemoBetaRecord

theorem escrowRegistryDemo_cancel_beta_step :
    EscrowRegistryCancelStep escrowRegistryDemoAfterReleaseAlpha
      escrowRegistryDemoAfterCancelBeta := by
  exact ⟨true, escrowRegistryDemoBetaRecord,
    escrowRegistryDemoAfterReleaseAlpha_beta, rfl, rfl⟩

theorem escrowRegistryDemoAfterCancelBeta_invariant :
    EscrowRegistryInvariant escrowRegistryDemoAfterCancelBeta := by
  exact escrowRegistryCancel_preserves_invariant
    escrowRegistryDemoAfterReleaseAlpha true escrowRegistryDemoBetaRecord
    escrowRegistryDemoAfterReleaseAlpha_invariant
    escrowRegistryDemoAfterReleaseAlpha_beta rfl

@[simp] theorem escrowRegistryDemoAfterCancelBeta_alpha :
    escrowRegistryDemoAfterCancelBeta.records false =
      some { escrowRegistryDemoAlphaRecord with phase := EscrowPhase.released } := by
  simp [escrowRegistryDemoAfterCancelBeta, escrowRegistryDemoAfterReleaseAlpha,
    escrowRegistryDemoAfterBoth, escrowRegistryDemoAfterAlpha,
    escrowRegistryDemoEmpty, emptyEscrowRegistry, escrowRegistryCancel,
    escrowRegistryRelease, escrowRegistryInsert]

@[simp] theorem escrowRegistryDemoAfterCancelBeta_beta :
    escrowRegistryDemoAfterCancelBeta.records true =
      some { escrowRegistryDemoBetaRecord with phase := EscrowPhase.cancelled } := by
  simp [escrowRegistryDemoAfterCancelBeta, escrowRegistryCancel]
/-! ## Pooled escrow reserve regressions -/
/-- Terminal escrow phases contribute zero to the pending reserve. -/
@[simp] theorem escrowPooledDemo_released_ne_pending :
    EscrowPhase.released ≠ EscrowPhase.pending := by
  decide

@[simp] theorem escrowPooledDemo_cancelled_ne_pending :
    EscrowPhase.cancelled ≠ EscrowPhase.pending := by
  decide



def escrowPooledDemoEmpty :
    PooledEscrowVaultState EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  { registry := escrowRegistryDemoEmpty
    vaultBalance := fun _ => 0 }

theorem escrowPooledDemoEmpty_invariant :
    PooledEscrowVaultInvariant escrowPooledDemoEmpty := by
  refine ⟨escrowRegistryDemoEmpty_invariant, ?_⟩
  intro asset
  simp [escrowPooledDemoEmpty, escrowRegistryDemoEmpty,
    emptyEscrowRegistry, pooledEscrowReserve, pooledEscrowContribution]

def escrowPooledDemoAfterAlpha :
    PooledEscrowVaultState EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  pooledEscrowVaultOpen escrowPooledDemoEmpty false escrowRegistryDemoAlphaRecord

theorem escrowPooledDemo_open_alpha_step :
    PooledEscrowVaultOpenStep escrowPooledDemoEmpty escrowPooledDemoAfterAlpha := by
  refine ⟨false, escrowRegistryDemoAlphaRecord, ?_, rfl, by decide, rfl⟩
  simp [escrowPooledDemoEmpty, escrowRegistryDemoEmpty, emptyEscrowRegistry]

theorem escrowPooledDemoAfterAlpha_invariant :
    PooledEscrowVaultInvariant escrowPooledDemoAfterAlpha := by
  exact pooledEscrowVaultOpen_preserves_invariant
    escrowPooledDemoEmpty_invariant escrowPooledDemo_open_alpha_step

def escrowPooledDemoAfterBoth :
    PooledEscrowVaultState EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  pooledEscrowVaultOpen escrowPooledDemoAfterAlpha true escrowRegistryDemoBetaRecord

theorem escrowPooledDemo_open_beta_step :
    PooledEscrowVaultOpenStep escrowPooledDemoAfterAlpha escrowPooledDemoAfterBoth := by
  refine ⟨true, escrowRegistryDemoBetaRecord, ?_, rfl, by decide, rfl⟩
  simp [escrowPooledDemoAfterAlpha, escrowPooledDemoEmpty,
    escrowRegistryDemoEmpty, emptyEscrowRegistry, escrowRegistryInsert,
    pooledEscrowVaultOpen]

theorem escrowPooledDemoAfterBoth_invariant :
    PooledEscrowVaultInvariant escrowPooledDemoAfterBoth := by
  exact pooledEscrowVaultOpen_preserves_invariant
    escrowPooledDemoAfterAlpha_invariant escrowPooledDemo_open_beta_step

theorem escrowPooledDemo_pooled_reserve_is_65 :
    pooledEscrowReserve escrowPooledDemoAfterBoth.registry EscrowDemoAsset.rft = 65 := by
  norm_num [pooledEscrowReserve, pooledEscrowContribution,
    escrowPooledDemoAfterBoth, escrowPooledDemoAfterAlpha,
    escrowPooledDemoEmpty, escrowRegistryDemoEmpty, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryInsert, pooledEscrowVaultOpen, escrowRegistryDemoAlphaRecord,
    escrowRegistryDemoBetaRecord]

def escrowPooledDemoAfterReleaseAlpha :
    PooledEscrowVaultState EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  pooledEscrowVaultRelease escrowPooledDemoAfterBoth false
    escrowRegistryDemoAlphaRecord

theorem escrowPooledDemo_release_alpha_step :
    PooledEscrowVaultReleaseStep escrowPooledDemoAfterBoth
      escrowPooledDemoAfterReleaseAlpha := by
  refine ⟨false, escrowRegistryDemoAlphaRecord, ?_, rfl, rfl⟩
  simp [escrowPooledDemoAfterBoth, escrowPooledDemoAfterAlpha,
    escrowPooledDemoEmpty, escrowRegistryDemoEmpty, emptyEscrowRegistry,
    escrowRegistryInsert, pooledEscrowVaultOpen]

theorem escrowPooledDemoAfterReleaseAlpha_invariant :
    PooledEscrowVaultInvariant escrowPooledDemoAfterReleaseAlpha := by
  exact pooledEscrowVaultRelease_preserves_invariant
    escrowPooledDemoAfterBoth_invariant escrowPooledDemo_release_alpha_step

theorem escrowPooledDemo_reserve_after_release_is_25 :
    pooledEscrowReserve escrowPooledDemoAfterReleaseAlpha.registry
      EscrowDemoAsset.rft = 25 := by
  norm_num [escrowPooledDemo_released_ne_pending,
    escrowPooledDemo_cancelled_ne_pending,
    pooledEscrowReserve, pooledEscrowContribution,
    escrowPooledDemoAfterReleaseAlpha, escrowPooledDemoAfterBoth,
    escrowPooledDemoAfterAlpha, escrowPooledDemoEmpty,
    escrowRegistryDemoEmpty, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryRelease, escrowRegistryInsert, pooledEscrowVaultRelease,
    pooledEscrowVaultOpen, escrowRegistryDemoAlphaRecord, escrowRegistryDemoBetaRecord]

def escrowPooledDemoAfterCancelBeta :
    PooledEscrowVaultState EscrowRegistryDemoId EscrowDemoHolder EscrowDemoAsset :=
  pooledEscrowVaultCancel escrowPooledDemoAfterReleaseAlpha true
    escrowRegistryDemoBetaRecord

theorem escrowPooledDemo_cancel_beta_step :
    PooledEscrowVaultCancelStep escrowPooledDemoAfterReleaseAlpha
      escrowPooledDemoAfterCancelBeta := by
  refine ⟨true, escrowRegistryDemoBetaRecord, ?_, rfl, rfl⟩
  simp [escrowPooledDemoAfterReleaseAlpha, escrowPooledDemoAfterBoth,
    escrowPooledDemoAfterAlpha, escrowPooledDemoEmpty,
    escrowRegistryDemoEmpty, emptyEscrowRegistry,
    escrowRegistryRelease, escrowRegistryInsert, pooledEscrowVaultRelease,
    pooledEscrowVaultOpen]

theorem escrowPooledDemoAfterCancelBeta_invariant :
    PooledEscrowVaultInvariant escrowPooledDemoAfterCancelBeta := by
  exact pooledEscrowVaultCancel_preserves_invariant
    escrowPooledDemoAfterReleaseAlpha_invariant escrowPooledDemo_cancel_beta_step

theorem escrowPooledDemo_reserve_after_both_terminal_is_zero :
    pooledEscrowReserve escrowPooledDemoAfterCancelBeta.registry
      EscrowDemoAsset.rft = 0 := by
  norm_num [escrowPooledDemo_released_ne_pending,
    escrowPooledDemo_cancelled_ne_pending,
    pooledEscrowReserve, pooledEscrowContribution,
    escrowPooledDemoAfterCancelBeta, escrowPooledDemoAfterReleaseAlpha,
    escrowPooledDemoAfterBoth, escrowPooledDemoAfterAlpha,
    escrowPooledDemoEmpty, escrowRegistryDemoEmpty, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryCancel, escrowRegistryRelease, escrowRegistryInsert,
    pooledEscrowVaultCancel, pooledEscrowVaultRelease, pooledEscrowVaultOpen,
    escrowRegistryDemoAlphaRecord, escrowRegistryDemoBetaRecord]
end SIRMTests

namespace SIRMTests

open SIRM

/-! ## Integrated pooled escrow / FinancialState / GL regression -/

abbrev IntegratedEscrowDemoId := Bool

def integratedEscrowDemoTransferPolicy :
    AuthorizationPolicy EscrowDemoPrincipal EscrowDemoHolder EscrowDemoAsset where
  mayTransfer := fun _ principal source destination asset amount =>
    (principal = EscrowDemoPrincipal.aliceOperator ∧
      source = EscrowDemoHolder.alice ∧ destination = EscrowDemoHolder.vault ∧
      asset = EscrowDemoAsset.rft ∧ (amount = 40 ∨ amount = 25)) ∨
    (principal = EscrowDemoPrincipal.escrowAgent ∧
      source = EscrowDemoHolder.vault ∧ destination = EscrowDemoHolder.bob ∧
      asset = EscrowDemoAsset.rft ∧ amount = 40) ∨
    (principal = EscrowDemoPrincipal.escrowAgent ∧
      source = EscrowDemoHolder.vault ∧ destination = EscrowDemoHolder.alice ∧
      asset = EscrowDemoAsset.rft ∧ amount = 25)
  mayIssue := fun _ _ _ _ _ _ => False
  mayBurn := fun _ _ _ _ _ => False

def integratedEscrowDemoPolicy :
    EscrowAuthorizationPolicy EscrowDemoPrincipal EscrowDemoHolder EscrowDemoAsset where
  mayOpenEscrow := fun _ principal depositor beneficiary vault asset amount =>
    (principal = EscrowDemoPrincipal.aliceOperator ∧
      depositor = EscrowDemoHolder.alice ∧ beneficiary = EscrowDemoHolder.bob ∧
      vault = EscrowDemoHolder.vault ∧ asset = EscrowDemoAsset.rft ∧ amount = 40) ∨
    (principal = EscrowDemoPrincipal.aliceOperator ∧
      depositor = EscrowDemoHolder.alice ∧ beneficiary = EscrowDemoHolder.treasury ∧
      vault = EscrowDemoHolder.vault ∧ asset = EscrowDemoAsset.rft ∧ amount = 25)
  mayReleaseEscrow := fun _ principal vault depositor beneficiary asset amount =>
    principal = EscrowDemoPrincipal.escrowAgent ∧
      vault = EscrowDemoHolder.vault ∧ depositor = EscrowDemoHolder.alice ∧
      beneficiary = EscrowDemoHolder.bob ∧ asset = EscrowDemoAsset.rft ∧ amount = 40
  mayCancelEscrow := fun _ principal vault depositor beneficiary asset amount =>
    principal = EscrowDemoPrincipal.escrowAgent ∧
      vault = EscrowDemoHolder.vault ∧ depositor = EscrowDemoHolder.alice ∧
      beneficiary = EscrowDemoHolder.treasury ∧ asset = EscrowDemoAsset.rft ∧ amount = 25

def integratedEscrowDemoInitialState :
    EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
      EscrowDemoHolder EscrowDemoAsset :=
  emptyEscrowFinancialRegistryState escrowDemoInitialFinancial

theorem integratedEscrowDemoInitial_invariant :
    EscrowFinancialRegistryInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault integratedEscrowDemoInitialState := by
  apply emptyEscrowFinancialRegistryInvariant_of_zero_vault
  · exact escrowDemoInitialFinancial_conservation
  · intro asset
    cases asset
    norm_num [integratedEscrowDemoInitialState, emptyEscrowFinancialRegistryState,
      escrowDemoInitialFinancial, escrowDemoInitialHoldings,
      issueToHolder, emptyHoldingsState]

theorem integratedEscrowDemo_alpha_transfer_authorized :
    integratedEscrowDemoTransferPolicy.mayTransfer
      integratedEscrowDemoInitialState.financial.holdings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.vault EscrowDemoAsset.rft 40 := by
  simp [integratedEscrowDemoTransferPolicy]

theorem integratedEscrowDemo_alpha_escrow_authorized :
    integratedEscrowDemoPolicy.mayOpenEscrow
      integratedEscrowDemoInitialState.financial.holdings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.bob EscrowDemoHolder.vault EscrowDemoAsset.rft 40 := by
  simp [integratedEscrowDemoPolicy]

theorem integratedEscrowDemo_alpha_funded :
    TransferAllowed integratedEscrowDemoInitialState.financial.holdings
      EscrowDemoHolder.alice EscrowDemoHolder.vault EscrowDemoAsset.rft 40 :=
  escrowDemo_open_funded

def integratedEscrowDemoAfterAlpha :
    EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
      EscrowDemoHolder EscrowDemoAsset :=
  escrowFinancialRegistryOpen integratedEscrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault integratedEscrowDemoInitialState false
    EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice EscrowDemoHolder.bob
    EscrowDemoAsset.rft 40 integratedEscrowDemo_alpha_transfer_authorized
    integratedEscrowDemo_alpha_funded

theorem integratedEscrowDemo_open_alpha_step :
    EscrowFinancialRegistryOpenStep integratedEscrowDemoTransferPolicy
      integratedEscrowDemoPolicy escrowDemoMapping EscrowDemoHolder.vault
      integratedEscrowDemoInitialState integratedEscrowDemoAfterAlpha := by
  refine ⟨false, EscrowDemoPrincipal.aliceOperator, EscrowDemoHolder.alice,
    EscrowDemoHolder.bob, EscrowDemoAsset.rft, 40, ?_, by decide, by decide,
    by decide, integratedEscrowDemo_alpha_transfer_authorized,
    integratedEscrowDemo_alpha_escrow_authorized,
    integratedEscrowDemo_alpha_funded, rfl⟩
  simp [integratedEscrowDemoInitialState, emptyEscrowFinancialRegistryState,
    emptyEscrowRegistry]

theorem integratedEscrowDemo_beta_transfer_authorized :
    integratedEscrowDemoTransferPolicy.mayTransfer
      integratedEscrowDemoAfterAlpha.financial.holdings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.vault EscrowDemoAsset.rft 25 := by
  simp [integratedEscrowDemoTransferPolicy]

theorem integratedEscrowDemo_beta_escrow_authorized :
    integratedEscrowDemoPolicy.mayOpenEscrow
      integratedEscrowDemoAfterAlpha.financial.holdings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice
      EscrowDemoHolder.treasury EscrowDemoHolder.vault EscrowDemoAsset.rft 25 := by
  simp [integratedEscrowDemoPolicy]

theorem integratedEscrowDemo_beta_funded :
    TransferAllowed integratedEscrowDemoAfterAlpha.financial.holdings
      EscrowDemoHolder.alice EscrowDemoHolder.vault EscrowDemoAsset.rft 25 := by
  right
  change (25 : Int) ≤ integratedEscrowDemoAfterAlpha.financial.holdings.balance
    EscrowDemoHolder.alice EscrowDemoAsset.rft
  norm_num [integratedEscrowDemoAfterAlpha, escrowFinancialRegistryOpen,
    escrowFinancialRegistryTransferFinancial, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
    executeAuthorizedTransfer, executeTransfer, transferBetweenHolders]

def integratedEscrowDemoAfterBoth :
    EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
      EscrowDemoHolder EscrowDemoAsset :=
  escrowFinancialRegistryOpen integratedEscrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault integratedEscrowDemoAfterAlpha true
    EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice EscrowDemoHolder.treasury
    EscrowDemoAsset.rft 25 integratedEscrowDemo_beta_transfer_authorized
    integratedEscrowDemo_beta_funded

theorem integratedEscrowDemo_open_beta_step :
    EscrowFinancialRegistryOpenStep integratedEscrowDemoTransferPolicy
      integratedEscrowDemoPolicy escrowDemoMapping EscrowDemoHolder.vault
      integratedEscrowDemoAfterAlpha integratedEscrowDemoAfterBoth := by
  refine ⟨true, EscrowDemoPrincipal.aliceOperator, EscrowDemoHolder.alice,
    EscrowDemoHolder.treasury, EscrowDemoAsset.rft, 25, ?_, by decide, by decide,
    by decide, integratedEscrowDemo_beta_transfer_authorized,
    integratedEscrowDemo_beta_escrow_authorized,
    integratedEscrowDemo_beta_funded, rfl⟩
  simp [integratedEscrowDemoAfterAlpha, escrowFinancialRegistryOpen,
    integratedEscrowDemoInitialState, emptyEscrowFinancialRegistryState,
    emptyEscrowRegistry, escrowRegistryInsert]

@[simp] theorem integratedEscrowDemoAfterBoth_alpha_record :
    integratedEscrowDemoAfterBoth.registry.records false =
      some (integratedPendingEscrowRecord EscrowDemoHolder.alice EscrowDemoHolder.bob
        EscrowDemoAsset.rft 40) := by
  simp [integratedEscrowDemoAfterBoth, integratedEscrowDemoAfterAlpha,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry, escrowRegistryInsert]

@[simp] theorem integratedEscrowDemoAfterBoth_beta_record :
    integratedEscrowDemoAfterBoth.registry.records true =
      some (integratedPendingEscrowRecord EscrowDemoHolder.alice
        EscrowDemoHolder.treasury EscrowDemoAsset.rft 25) := by
  simp [integratedEscrowDemoAfterBoth, integratedEscrowDemoAfterAlpha,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry, escrowRegistryInsert]

theorem integratedEscrowDemo_alpha_release_transfer_authorized :
    integratedEscrowDemoTransferPolicy.mayTransfer
      integratedEscrowDemoAfterBoth.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  simp [integratedEscrowDemoTransferPolicy]

theorem integratedEscrowDemo_alpha_release_escrow_authorized :
    integratedEscrowDemoPolicy.mayReleaseEscrow
      integratedEscrowDemoAfterBoth.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  simp [integratedEscrowDemoPolicy]

theorem integratedEscrowDemo_alpha_release_funded :
    TransferAllowed integratedEscrowDemoAfterBoth.financial.holdings
      EscrowDemoHolder.vault EscrowDemoHolder.bob EscrowDemoAsset.rft 40 := by
  right
  change (40 : Int) ≤ integratedEscrowDemoAfterBoth.financial.holdings.balance
    EscrowDemoHolder.vault EscrowDemoAsset.rft
  norm_num [integratedEscrowDemoAfterBoth, integratedEscrowDemoAfterAlpha,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
    escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
    executeTransfer, transferBetweenHolders]

def integratedEscrowDemoAfterReleaseAlpha :
    EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
      EscrowDemoHolder EscrowDemoAsset :=
  escrowFinancialRegistryRelease integratedEscrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault integratedEscrowDemoAfterBoth false
    (integratedPendingEscrowRecord EscrowDemoHolder.alice EscrowDemoHolder.bob
      EscrowDemoAsset.rft 40)
    EscrowDemoPrincipal.escrowAgent
    integratedEscrowDemo_alpha_release_transfer_authorized
    integratedEscrowDemo_alpha_release_funded

theorem integratedEscrowDemo_release_alpha_step :
    EscrowFinancialRegistryReleaseStep integratedEscrowDemoTransferPolicy
      integratedEscrowDemoPolicy escrowDemoMapping EscrowDemoHolder.vault
      integratedEscrowDemoAfterBoth integratedEscrowDemoAfterReleaseAlpha := by
  refine ⟨false,
    integratedPendingEscrowRecord EscrowDemoHolder.alice EscrowDemoHolder.bob
      EscrowDemoAsset.rft 40,
    EscrowDemoPrincipal.escrowAgent,
    integratedEscrowDemoAfterBoth_alpha_record, rfl,
    integratedEscrowDemo_alpha_release_transfer_authorized,
    integratedEscrowDemo_alpha_release_escrow_authorized,
    integratedEscrowDemo_alpha_release_funded, rfl⟩

theorem integratedEscrowDemo_beta_cancel_transfer_authorized :
    integratedEscrowDemoTransferPolicy.mayTransfer
      integratedEscrowDemoAfterReleaseAlpha.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoAsset.rft 25 := by
  simp [integratedEscrowDemoTransferPolicy]

theorem integratedEscrowDemo_beta_cancel_escrow_authorized :
    integratedEscrowDemoPolicy.mayCancelEscrow
      integratedEscrowDemoAfterReleaseAlpha.financial.holdings
      EscrowDemoPrincipal.escrowAgent EscrowDemoHolder.vault
      EscrowDemoHolder.alice EscrowDemoHolder.treasury EscrowDemoAsset.rft 25 := by
  simp [integratedEscrowDemoPolicy]

theorem integratedEscrowDemo_beta_cancel_funded :
    TransferAllowed integratedEscrowDemoAfterReleaseAlpha.financial.holdings
      EscrowDemoHolder.vault EscrowDemoHolder.alice EscrowDemoAsset.rft 25 := by
  right
  have hVaultBalance :
      integratedEscrowDemoAfterReleaseAlpha.financial.holdings.balance
        EscrowDemoHolder.vault EscrowDemoAsset.rft = 25 := by
    norm_num [integratedEscrowDemoAfterReleaseAlpha, integratedEscrowDemoAfterBoth,
      integratedEscrowDemoAfterAlpha, escrowFinancialRegistryRelease,
      escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
      emptyEscrowFinancialRegistryState, escrowDemoInitialFinancial,
      escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState,
      escrowFinancialRegistryTransferFinancial, executeAuthorizedTransfer,
      executeTransfer, transferBetweenHolders, integratedPendingEscrowRecord]
  change (25 : Int) ≤ integratedEscrowDemoAfterReleaseAlpha.financial.holdings.balance
    EscrowDemoHolder.vault EscrowDemoAsset.rft
  rw [hVaultBalance]

def integratedEscrowDemoAfterCancelBeta :
    EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
      EscrowDemoHolder EscrowDemoAsset :=
  escrowFinancialRegistryCancel integratedEscrowDemoTransferPolicy escrowDemoMapping
    EscrowDemoHolder.vault integratedEscrowDemoAfterReleaseAlpha true
    (integratedPendingEscrowRecord EscrowDemoHolder.alice EscrowDemoHolder.treasury
      EscrowDemoAsset.rft 25)
    EscrowDemoPrincipal.escrowAgent
    integratedEscrowDemo_beta_cancel_transfer_authorized
    integratedEscrowDemo_beta_cancel_funded

theorem integratedEscrowDemo_cancel_beta_step :
    EscrowFinancialRegistryCancelStep integratedEscrowDemoTransferPolicy
      integratedEscrowDemoPolicy escrowDemoMapping EscrowDemoHolder.vault
      integratedEscrowDemoAfterReleaseAlpha integratedEscrowDemoAfterCancelBeta := by
  refine ⟨true,
    integratedPendingEscrowRecord EscrowDemoHolder.alice EscrowDemoHolder.treasury
      EscrowDemoAsset.rft 25,
    EscrowDemoPrincipal.escrowAgent,
    ?_, rfl,
    integratedEscrowDemo_beta_cancel_transfer_authorized,
    integratedEscrowDemo_beta_cancel_escrow_authorized,
    integratedEscrowDemo_beta_cancel_funded, rfl⟩
  simp [integratedEscrowDemoAfterReleaseAlpha, integratedEscrowDemoAfterBoth,
    integratedEscrowDemoAfterAlpha, escrowFinancialRegistryRelease,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry, escrowRegistryInsert,
    escrowRegistryRelease]

def integratedEscrowDemoMachine :
    VerifiedStateMachine
      (EscrowFinancialRegistryState IntegratedEscrowDemoId EscrowDemoHolder
        EscrowDemoHolder EscrowDemoAsset) :=
  escrowFinancialRegistryMachine integratedEscrowDemoTransferPolicy
    integratedEscrowDemoPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault integratedEscrowDemoInitialState
    integratedEscrowDemoInitial_invariant

theorem integratedEscrowDemo_initial_reachable :
    Reachable integratedEscrowDemoMachine integratedEscrowDemoInitialState :=
  Reachable.initial rfl

theorem integratedEscrowDemo_after_alpha_reachable :
    Reachable integratedEscrowDemoMachine integratedEscrowDemoAfterAlpha :=
  Reachable.step integratedEscrowDemo_initial_reachable
    (Or.inl integratedEscrowDemo_open_alpha_step)

theorem integratedEscrowDemo_after_both_reachable :
    Reachable integratedEscrowDemoMachine integratedEscrowDemoAfterBoth :=
  Reachable.step integratedEscrowDemo_after_alpha_reachable
    (Or.inl integratedEscrowDemo_open_beta_step)

theorem integratedEscrowDemo_after_release_reachable :
    Reachable integratedEscrowDemoMachine integratedEscrowDemoAfterReleaseAlpha :=
  Reachable.step integratedEscrowDemo_after_both_reachable
    (Or.inr (Or.inl integratedEscrowDemo_release_alpha_step))

theorem integratedEscrowDemo_after_cancel_reachable :
    Reachable integratedEscrowDemoMachine integratedEscrowDemoAfterCancelBeta :=
  Reachable.step integratedEscrowDemo_after_release_reachable
    (Or.inr (Or.inr integratedEscrowDemo_cancel_beta_step))

theorem integratedEscrowDemo_after_both_invariant :
    EscrowFinancialRegistryInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault integratedEscrowDemoAfterBoth :=
  escrowFinancialRegistryInvariant_of_reachable integratedEscrowDemoTransferPolicy
    integratedEscrowDemoPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault integratedEscrowDemoInitialState
    integratedEscrowDemoInitial_invariant integratedEscrowDemo_after_both_reachable

theorem integratedEscrowDemo_after_release_invariant :
    EscrowFinancialRegistryInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault integratedEscrowDemoAfterReleaseAlpha :=
  escrowFinancialRegistryInvariant_of_reachable integratedEscrowDemoTransferPolicy
    integratedEscrowDemoPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault integratedEscrowDemoInitialState
    integratedEscrowDemoInitial_invariant integratedEscrowDemo_after_release_reachable

theorem integratedEscrowDemo_after_cancel_invariant :
    EscrowFinancialRegistryInvariant escrowDemoMapping escrowDemoOpeningLedger
      EscrowDemoHolder.vault integratedEscrowDemoAfterCancelBeta :=
  escrowFinancialRegistryInvariant_of_reachable integratedEscrowDemoTransferPolicy
    integratedEscrowDemoPolicy escrowDemoMapping escrowDemoOpeningLedger
    EscrowDemoHolder.vault integratedEscrowDemoInitialState
    integratedEscrowDemoInitial_invariant integratedEscrowDemo_after_cancel_reachable

theorem integratedEscrowDemo_pending_reserve_65 :
    pooledEscrowReserve integratedEscrowDemoAfterBoth.registry EscrowDemoAsset.rft = 65 := by
  norm_num [pooledEscrowReserve, pooledEscrowContribution,
    integratedEscrowDemoAfterBoth, integratedEscrowDemoAfterAlpha,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryInsert, integratedPendingEscrowRecord]

theorem integratedEscrowDemo_pending_reserve_after_release_25 :
    pooledEscrowReserve integratedEscrowDemoAfterReleaseAlpha.registry
      EscrowDemoAsset.rft = 25 := by
  norm_num [escrowPooledDemo_released_ne_pending,
    escrowPooledDemo_cancelled_ne_pending,
    pooledEscrowReserve, pooledEscrowContribution,
    integratedEscrowDemoAfterReleaseAlpha, integratedEscrowDemoAfterBoth,
    integratedEscrowDemoAfterAlpha, escrowFinancialRegistryRelease,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryRelease, escrowRegistryInsert,
    integratedPendingEscrowRecord]

theorem integratedEscrowDemo_pending_reserve_after_cancel_zero :
    pooledEscrowReserve integratedEscrowDemoAfterCancelBeta.registry
      EscrowDemoAsset.rft = 0 := by
  norm_num [escrowPooledDemo_released_ne_pending,
    escrowPooledDemo_cancelled_ne_pending,
    pooledEscrowReserve, pooledEscrowContribution,
    integratedEscrowDemoAfterCancelBeta, integratedEscrowDemoAfterReleaseAlpha,
    integratedEscrowDemoAfterBoth, integratedEscrowDemoAfterAlpha,
    escrowFinancialRegistryCancel, escrowFinancialRegistryRelease,
    escrowFinancialRegistryOpen, integratedEscrowDemoInitialState,
    emptyEscrowFinancialRegistryState, emptyEscrowRegistry,
    Fin.sum_univ_succ, escrowRegistryCancel, escrowRegistryRelease,
    escrowRegistryInsert, integratedPendingEscrowRecord]

theorem integratedEscrowDemo_after_both_vault_gl_pool_65 :
    integratedEscrowDemoAfterBoth.financial.holdings.balance
        EscrowDemoHolder.vault EscrowDemoAsset.rft = 65 ∧
    integratedEscrowDemoAfterBoth.financial.ledger.balance
        (escrowDemoMapping.ledgerAccount EscrowDemoHolder.vault)
        EscrowDemoAsset.rft = 65 ∧
    pooledEscrowReserve integratedEscrowDemoAfterBoth.registry
        EscrowDemoAsset.rft = 65 := by
  have hInvariant := integratedEscrowDemo_after_both_invariant
  have hBridge := escrowFinancialRegistryVault_gl_equals_pending
    escrowDemoMapping escrowDemoOpeningLedger EscrowDemoHolder.vault
    integratedEscrowDemoAfterBoth hInvariant EscrowDemoAsset.rft
  have hPool := integratedEscrowDemo_pending_reserve_65
  refine ⟨?_, ?_, hPool⟩
  · rw [hInvariant.vault_matches_pending, hPool]
  · rw [hBridge.2, hPool]

theorem integratedEscrowDemo_after_release_vault_gl_pool_25 :
    integratedEscrowDemoAfterReleaseAlpha.financial.holdings.balance
        EscrowDemoHolder.vault EscrowDemoAsset.rft = 25 ∧
    integratedEscrowDemoAfterReleaseAlpha.financial.ledger.balance
        (escrowDemoMapping.ledgerAccount EscrowDemoHolder.vault)
        EscrowDemoAsset.rft = 25 ∧
    pooledEscrowReserve integratedEscrowDemoAfterReleaseAlpha.registry
        EscrowDemoAsset.rft = 25 := by
  have hInvariant := integratedEscrowDemo_after_release_invariant
  have hBridge := escrowFinancialRegistryVault_gl_equals_pending
    escrowDemoMapping escrowDemoOpeningLedger EscrowDemoHolder.vault
    integratedEscrowDemoAfterReleaseAlpha hInvariant EscrowDemoAsset.rft
  have hPool := integratedEscrowDemo_pending_reserve_after_release_25
  refine ⟨?_, ?_, hPool⟩
  · rw [hInvariant.vault_matches_pending, hPool]
  · rw [hBridge.2, hPool]

theorem integratedEscrowDemo_after_cancel_vault_gl_pool_zero :
    integratedEscrowDemoAfterCancelBeta.financial.holdings.balance
        EscrowDemoHolder.vault EscrowDemoAsset.rft = 0 ∧
    integratedEscrowDemoAfterCancelBeta.financial.ledger.balance
        (escrowDemoMapping.ledgerAccount EscrowDemoHolder.vault)
        EscrowDemoAsset.rft = 0 ∧
    pooledEscrowReserve integratedEscrowDemoAfterCancelBeta.registry
        EscrowDemoAsset.rft = 0 := by
  have hInvariant := integratedEscrowDemo_after_cancel_invariant
  have hBridge := escrowFinancialRegistryVault_gl_equals_pending
    escrowDemoMapping escrowDemoOpeningLedger EscrowDemoHolder.vault
    integratedEscrowDemoAfterCancelBeta hInvariant EscrowDemoAsset.rft
  have hPool := integratedEscrowDemo_pending_reserve_after_cancel_zero
  refine ⟨?_, ?_, hPool⟩
  · rw [hInvariant.vault_matches_pending, hPool]
  · rw [hBridge.2, hPool]

end SIRMTests
namespace SIRMTests

open SIRM

/-! ## Global per-principal nonce across transfer / issue / burn -/

abbrev ReplayFinancialDemoState :=
  ReplayProtectedFinancialState EscrowDemoPrincipal EscrowDemoHolder
    EscrowDemoHolder EscrowDemoAsset

def replayFinancialDemoInitial : ReplayFinancialDemoState :=
  initialReplayProtectedFinancialState EscrowDemoPrincipal escrowDemoInitialFinancial

def replayFinancialDemoFinancialAfter :
    FinancialState EscrowDemoHolder EscrowDemoHolder EscrowDemoAsset :=
  { holdings := executeAuthorizedTransfer integratedEscrowDemoTransferPolicy
      replayFinancialDemoInitial.financial.holdings
      EscrowDemoPrincipal.aliceOperator EscrowDemoHolder.alice EscrowDemoHolder.vault
      EscrowDemoAsset.rft 40 integratedEscrowDemo_alpha_transfer_authorized
      integratedEscrowDemo_alpha_funded
    ledger := postJournal replayFinancialDemoInitial.financial.ledger
      (holderTransferJournal escrowDemoMapping EscrowDemoHolder.alice
        EscrowDemoHolder.vault EscrowDemoAsset.rft 40) }

theorem replayFinancialDemo_financial_step :
    AuthorizedFinancialStep integratedEscrowDemoTransferPolicy escrowDemoMapping
      EscrowDemoHolder.treasury replayFinancialDemoInitial.financial
      replayFinancialDemoFinancialAfter := by
  apply Or.inl
  refine ⟨EscrowDemoPrincipal.aliceOperator, EscrowDemoHolder.alice,
    EscrowDemoHolder.vault, EscrowDemoAsset.rft, 40, ?_, ?_, rfl⟩
  · simpa [replayFinancialDemoInitial, initialReplayProtectedFinancialState,
      integratedEscrowDemoInitialState, emptyEscrowFinancialRegistryState] using
      integratedEscrowDemo_alpha_transfer_authorized
  · simpa [replayFinancialDemoInitial, initialReplayProtectedFinancialState,
      integratedEscrowDemoInitialState, emptyEscrowFinancialRegistryState] using
      integratedEscrowDemo_alpha_funded

def replayFinancialDemoAfter : ReplayFinancialDemoState :=
  applyReplayProtectedFinancialStep EscrowDemoPrincipal replayFinancialDemoInitial
    EscrowDemoPrincipal.aliceOperator 0 replayFinancialDemoFinancialAfter

theorem replayFinancialDemo_step :
    ReplayProtectedFinancialStep integratedEscrowDemoTransferPolicy escrowDemoMapping
      EscrowDemoHolder.treasury EscrowDemoPrincipal.aliceOperator 0
      replayFinancialDemoInitial replayFinancialDemoAfter := by
  refine ⟨?_, replayFinancialDemoFinancialAfter, replayFinancialDemo_financial_step, rfl⟩
  simp [replayFinancialDemoInitial, initialReplayProtectedFinancialState]

def replayFinancialDemoMachine :
    VerifiedStateMachine ReplayFinancialDemoState :=
  replayProtectedFinancialMachine (Principal := EscrowDemoPrincipal)
    integratedEscrowDemoTransferPolicy escrowDemoMapping EscrowDemoHolder.treasury
    escrowDemoInitialFinancial escrowDemoInitialFinancial_conservation.1

theorem replayFinancialDemo_initial_reachable :
    Reachable replayFinancialDemoMachine replayFinancialDemoInitial :=
  Reachable.initial rfl

theorem replayFinancialDemo_after_reachable :
    Reachable replayFinancialDemoMachine replayFinancialDemoAfter :=
  Reachable.step replayFinancialDemo_initial_reachable
    ⟨EscrowDemoPrincipal.aliceOperator, 0, replayFinancialDemo_step⟩

theorem replayFinancialDemo_accepted_nonce_is_one :
    replayFinancialDemoAfter.nextNonce EscrowDemoPrincipal.aliceOperator = 1 := by
  exact replayProtectedFinancialStep_next_nonce
    integratedEscrowDemoTransferPolicy escrowDemoMapping EscrowDemoHolder.treasury
    EscrowDemoPrincipal.aliceOperator 0 replayFinancialDemo_step

theorem replayFinancialDemo_other_principal_nonce_stays_zero :
    replayFinancialDemoAfter.nextNonce EscrowDemoPrincipal.escrowAgent = 0 := by
  have h := replayProtectedFinancialStep_other_nonce
    integratedEscrowDemoTransferPolicy escrowDemoMapping EscrowDemoHolder.treasury
    EscrowDemoPrincipal.aliceOperator EscrowDemoPrincipal.escrowAgent 0
    replayFinancialDemo_step (by decide)
  simpa [replayFinancialDemoInitial, initialReplayProtectedFinancialState] using h

theorem replayFinancialDemo_stale_nonce_rejected (after : ReplayFinancialDemoState) :
    ¬ ReplayProtectedFinancialStep integratedEscrowDemoTransferPolicy escrowDemoMapping
      EscrowDemoHolder.treasury EscrowDemoPrincipal.aliceOperator 0
      replayFinancialDemoAfter after := by
  apply replayProtectedFinancialStep_reject_nonce_mismatch
  norm_num [replayFinancialDemoAfter, applyReplayProtectedFinancialStep]

theorem replayFinancialDemo_future_nonce_rejected (after : ReplayFinancialDemoState) :
    ¬ ReplayProtectedFinancialStep integratedEscrowDemoTransferPolicy escrowDemoMapping
      EscrowDemoHolder.treasury EscrowDemoPrincipal.aliceOperator 1
      replayFinancialDemoInitial after := by
  apply replayProtectedFinancialStep_reject_nonce_mismatch
  norm_num [replayFinancialDemoInitial, initialReplayProtectedFinancialState]

theorem replayFinancialDemo_vault_balance_is_forty :
    replayFinancialDemoAfter.financial.holdings.balance
      EscrowDemoHolder.vault EscrowDemoAsset.rft = 40 := by
  norm_num [replayFinancialDemoAfter, applyReplayProtectedFinancialStep,
    replayFinancialDemoFinancialAfter, replayFinancialDemoInitial,
    initialReplayProtectedFinancialState, executeAuthorizedTransfer,
    executeTransfer, transferBetweenHolders, escrowDemoInitialFinancial,
    escrowDemoInitialHoldings, issueToHolder, emptyHoldingsState]

theorem replayFinancialDemo_invariant_reachable :
    ReplayProtectedFinancialInvariant escrowDemoMapping escrowDemoOpeningLedger
      replayFinancialDemoAfter :=
  replayProtectedFinancialInvariant_of_reachable
    integratedEscrowDemoTransferPolicy escrowDemoMapping EscrowDemoHolder.treasury
    escrowDemoInitialFinancial escrowDemoInitialFinancial_conservation.1
    replayFinancialDemo_after_reachable

/-! ## Typed financial transaction-envelope regressions -/

def demoFinancialEnvelopeRequest :
    FinancialTransactionRequest DemoPrincipal DemoAccount DemoAsset :=
  { principal := DemoPrincipal.alice
    nonce := 0
    operation := .transfer DemoAccount.alice DemoAccount.bob DemoAsset.rft 40 }

theorem demoFinancialEnvelope_transfer_operation_step :
    FinancialOperationStep demoAuthorizationPolicy demoHolderLedgerMap
      DemoLedgerAccount.control DemoPrincipal.alice
      (.transfer DemoAccount.alice DemoAccount.bob DemoAsset.rft 40)
      demoInitialFinancialState demoFinancialAfterTransfer := by
  exact ⟨demoAliceMayTransferFromAlice, transfer40_is_funded, rfl⟩

def demoFinancialEnvelopeInitialState :
    FinancialTransactionEnvelopeState Nat DemoPrincipal DemoAccount
      DemoLedgerAccount DemoAsset :=
  initialFinancialTransactionEnvelopeState Nat DemoPrincipal demoInitialFinancialState

def demoFinancialEnvelopeAfterTransfer :
    FinancialTransactionEnvelopeState Nat DemoPrincipal DemoAccount
      DemoLedgerAccount DemoAsset :=
  applyFinancialTransactionSuccess DemoPrincipal Nat
    demoFinancialEnvelopeInitialState 17 demoFinancialEnvelopeRequest
    demoFinancialAfterTransfer

theorem demoFinancialEnvelope_transfer_success :
    FinancialTransactionEnvelopeSuccessStep demoAuthorizationPolicy
      demoHolderLedgerMap DemoLedgerAccount.control 17
      demoFinancialEnvelopeRequest demoFinancialEnvelopeInitialState
      demoFinancialEnvelopeAfterTransfer := by
  refine ⟨?_, ?_, demoFinancialAfterTransfer,
    demoFinancialEnvelope_transfer_operation_step, rfl⟩
  · simp [demoFinancialEnvelopeInitialState,
      initialFinancialTransactionEnvelopeState]
  · simp [demoFinancialEnvelopeRequest, demoFinancialEnvelopeInitialState,
      initialFinancialTransactionEnvelopeState,
      initialReplayProtectedFinancialState]

theorem demoFinancialEnvelope_receipt_stored :
    demoFinancialEnvelopeAfterTransfer.receipts 17 =
      some (acceptedFinancialTransactionReceipt 17 demoFinancialEnvelopeRequest) :=
  financialTransactionEnvelopeSuccess_stores_receipt
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    17 demoFinancialEnvelopeRequest demoFinancialEnvelope_transfer_success

theorem demoFinancialEnvelope_exact_retry_is_step :
    FinancialTransactionEnvelopeReplayStep 17 demoFinancialEnvelopeRequest
      demoFinancialEnvelopeAfterTransfer demoFinancialEnvelopeAfterTransfer := by
  exact ⟨acceptedFinancialTransactionReceipt 17 demoFinancialEnvelopeRequest,
    demoFinancialEnvelope_receipt_stored, rfl, rfl, rfl⟩

theorem demoFinancialEnvelope_exact_retry_returns_cached_response :
    cachedFinancialTransactionResponse demoFinancialEnvelopeAfterTransfer 17
      demoFinancialEnvelopeRequest =
        some (acceptedFinancialTransactionResponse 17 demoFinancialEnvelopeRequest) := by
  simp [cachedFinancialTransactionResponse,
    acceptedFinancialTransactionReceipt,
    acceptedFinancialTransactionResponse,
    demoFinancialEnvelope_receipt_stored]

theorem demoFinancialEnvelope_exact_retry_changes_no_state :
    ∀ afterRetry,
      FinancialTransactionEnvelopeReplayStep 17 demoFinancialEnvelopeRequest
        demoFinancialEnvelopeAfterTransfer afterRetry →
      afterRetry = demoFinancialEnvelopeAfterTransfer := by
  intro afterRetry hReplay
  exact financialTransactionEnvelopeReplay_state_unchanged
    demoFinancialEnvelopeAfterTransfer afterRetry
    17 demoFinancialEnvelopeRequest hReplay

def demoFinancialEnvelopeConflictingRequest :
    FinancialTransactionRequest DemoPrincipal DemoAccount DemoAsset :=
  { demoFinancialEnvelopeRequest with
    operation := .burn DemoAccount.alice DemoAsset.rft 20 }

theorem demoFinancialEnvelope_request_id_conflict :
    FinancialTransactionRequestIdConflict demoFinancialEnvelopeAfterTransfer 17
      demoFinancialEnvelopeConflictingRequest := by
  refine ⟨acceptedFinancialTransactionReceipt 17 demoFinancialEnvelopeRequest,
    demoFinancialEnvelope_receipt_stored, ?_⟩
  decide

theorem demoFinancialEnvelope_conflicting_payload_rejected :
    ∀ next,
      ¬ FinancialTransactionEnvelopeSuccessStep demoAuthorizationPolicy
        demoHolderLedgerMap DemoLedgerAccount.control 17
        demoFinancialEnvelopeConflictingRequest
        demoFinancialEnvelopeAfterTransfer next := by
  intro next
  exact financialTransactionEnvelopeConflict_rejects_success
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    17 demoFinancialEnvelopeConflictingRequest demoFinancialEnvelopeAfterTransfer
    next demoFinancialEnvelope_request_id_conflict

theorem demoFinancialEnvelope_same_nonce_competitor_rejected :
    ∀ next,
      ¬ FinancialTransactionEnvelopeSuccessStep demoAuthorizationPolicy
        demoHolderLedgerMap DemoLedgerAccount.control 18
        demoFinancialEnvelopeConflictingRequest
        demoFinancialEnvelopeAfterTransfer next := by
  intro next
  exact financialTransactionEnvelopeSuccess_rejects_same_nonce_competitor
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    17 18 demoFinancialEnvelopeRequest demoFinancialEnvelopeConflictingRequest
    demoFinancialEnvelopeInitialState demoFinancialEnvelopeAfterTransfer next
    demoFinancialEnvelope_transfer_success rfl rfl

theorem demoFinancialEnvelope_other_principal_nonce_unchanged :
    demoFinancialEnvelopeAfterTransfer.core.nextNonce DemoPrincipal.bob = 0 :=
  financialTransactionEnvelopeSuccess_other_nonce
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    17 demoFinancialEnvelopeRequest DemoPrincipal.bob
    demoFinancialEnvelope_transfer_success (by decide)

theorem demoFinancialEnvelope_next_nonce_is_one :
    demoFinancialEnvelopeAfterTransfer.core.nextNonce DemoPrincipal.alice = 1 :=
  financialTransactionEnvelopeSuccess_advances_nonce
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    17 demoFinancialEnvelopeRequest demoFinancialEnvelope_transfer_success

theorem demoFinancialEnvelope_old_nonce_new_id_rejected :
    ∀ next,
      ¬ FinancialTransactionEnvelopeSuccessStep demoAuthorizationPolicy
        demoHolderLedgerMap DemoLedgerAccount.control 18
        demoFinancialEnvelopeRequest demoFinancialEnvelopeAfterTransfer next := by
  intro next
  apply financialTransactionEnvelopeNonceMismatch_rejects_success
  simp [demoFinancialEnvelopeRequest, demoFinancialEnvelope_next_nonce_is_one]

theorem demoFinancialEnvelope_retry_payload_nonce_is_stale :
    demoFinancialEnvelopeRequest.nonce ≠
      demoFinancialEnvelopeAfterTransfer.core.nextNonce DemoPrincipal.alice := by
  rw [demoFinancialEnvelope_next_nonce_is_one]
  simp [demoFinancialEnvelopeRequest]

def demoFinancialEnvelopeMachine :
    VerifiedStateMachine
      (FinancialTransactionEnvelopeState Nat DemoPrincipal DemoAccount
        DemoLedgerAccount DemoAsset) :=
  financialTransactionEnvelopeMachine demoAuthorizationPolicy demoHolderLedgerMap
    DemoLedgerAccount.control demoInitialFinancialState
    demoInitialFinancialState_invariant

theorem demoFinancialEnvelope_initial_reachable :
    Reachable demoFinancialEnvelopeMachine demoFinancialEnvelopeInitialState :=
  Reachable.initial rfl

theorem demoFinancialEnvelope_after_transfer_reachable :
    Reachable demoFinancialEnvelopeMachine demoFinancialEnvelopeAfterTransfer :=
  Reachable.step demoFinancialEnvelope_initial_reachable
    (Or.inl ⟨17, demoFinancialEnvelopeRequest,
      demoFinancialEnvelope_transfer_success⟩)

theorem demoFinancialEnvelope_after_retry_reachable :
    Reachable demoFinancialEnvelopeMachine demoFinancialEnvelopeAfterTransfer :=
  Reachable.step demoFinancialEnvelope_after_transfer_reachable
    (Or.inr ⟨17, demoFinancialEnvelopeRequest,
      demoFinancialEnvelope_exact_retry_is_step⟩)

theorem demoFinancialEnvelope_reachable_state_preserves_conservation :
    FinancialTransactionEnvelopeInvariant demoHolderLedgerMap
      demoInitialFinancialState.ledger demoFinancialEnvelopeAfterTransfer :=
  financialTransactionEnvelopeInvariant_of_reachable
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    demoInitialFinancialState demoInitialFinancialState_invariant
    demoFinancialEnvelope_after_retry_reachable


/-! ## Cached authorization-denial transaction-envelope regressions -/

def demoFinancialProcessorDeniedPolicy :
    AuthorizationPolicy DemoPrincipal DemoAccount DemoAsset :=
  { demoAuthorizationPolicy with
    mayTransfer := fun _ _ _ _ _ _ => False }

def demoFinancialProcessorInitialState :
    FinancialTransactionProcessorState Nat DemoPrincipal DemoAccount
      DemoLedgerAccount DemoAsset :=
  initialFinancialTransactionProcessorState Nat DemoPrincipal
    demoInitialFinancialState

def demoFinancialProcessorAfterDenial :
    FinancialTransactionProcessorState Nat DemoPrincipal DemoAccount
      DemoLedgerAccount DemoAsset :=
  applyFinancialTransactionAuthorizationDenial
    demoFinancialProcessorInitialState 17 demoFinancialEnvelopeRequest
    .transferAuthorizationDenied

theorem demoFinancialProcessor_transfer_is_authorization_denied :
    FinancialTransactionAuthorizationDenial
      demoFinancialProcessorDeniedPolicy demoFinancialEnvelopeRequest
      demoInitialFinancialState .transferAuthorizationDenied := by
  simp [FinancialTransactionAuthorizationDenial,
    demoFinancialProcessorDeniedPolicy, demoFinancialEnvelopeRequest]

theorem demoFinancialProcessor_denial_is_admitted_at_current_nonce :
    FinancialTransactionAuthorizationDenialStep demoFinancialProcessorDeniedPolicy
      17 demoFinancialEnvelopeRequest .transferAuthorizationDenied
      demoFinancialProcessorInitialState demoFinancialProcessorAfterDenial := by
  refine ⟨?_, ?_, ?_, demoFinancialProcessor_transfer_is_authorization_denied, rfl⟩
  · simp [demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState,
      initialFinancialTransactionEnvelopeState]
  · simp [demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState]
  · simp [demoFinancialEnvelopeRequest, demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState,
      initialFinancialTransactionEnvelopeState,
      initialReplayProtectedFinancialState]

theorem demoFinancialProcessor_denial_does_not_consume_nonce :
    demoFinancialProcessorAfterDenial.envelope.core.nextNonce DemoPrincipal.alice = 0 := by
  rw [financialTransactionAuthorizationDenial_core_unchanged
    demoFinancialProcessorDeniedPolicy demoFinancialProcessorInitialState
    demoFinancialProcessorAfterDenial 17 demoFinancialEnvelopeRequest
    .transferAuthorizationDenied
    demoFinancialProcessor_denial_is_admitted_at_current_nonce]
  simp [demoFinancialProcessorInitialState,
    initialFinancialTransactionProcessorState,
    initialFinancialTransactionEnvelopeState,
    initialReplayProtectedFinancialState]

theorem demoFinancialProcessor_denial_does_not_change_financial_state :
    demoFinancialProcessorAfterDenial.envelope.core.financial =
      demoInitialFinancialState := by
  rw [financialTransactionAuthorizationDenial_core_unchanged
    demoFinancialProcessorDeniedPolicy demoFinancialProcessorInitialState
    demoFinancialProcessorAfterDenial 17 demoFinancialEnvelopeRequest
    .transferAuthorizationDenied
    demoFinancialProcessor_denial_is_admitted_at_current_nonce]
  simp [demoFinancialProcessorInitialState,
    initialFinancialTransactionProcessorState,
    initialFinancialTransactionEnvelopeState,
    initialReplayProtectedFinancialState]

def demoFinancialProcessorAfterNewIdSuccess :
    FinancialTransactionProcessorState Nat DemoPrincipal DemoAccount
      DemoLedgerAccount DemoAsset :=
  { envelope := applyFinancialTransactionSuccess DemoPrincipal Nat
      demoFinancialProcessorAfterDenial.envelope 18 demoFinancialEnvelopeRequest
      demoFinancialAfterTransfer
    denials := demoFinancialProcessorAfterDenial.denials }

theorem demoFinancialProcessor_underlying_success_with_new_id :
    FinancialTransactionEnvelopeSuccessStep demoAuthorizationPolicy
      demoHolderLedgerMap DemoLedgerAccount.control 18
      demoFinancialEnvelopeRequest demoFinancialProcessorAfterDenial.envelope
      demoFinancialProcessorAfterNewIdSuccess.envelope := by
  refine ⟨?_, ?_, demoFinancialAfterTransfer,
    demoFinancialEnvelope_transfer_operation_step, rfl⟩
  · simp [demoFinancialProcessorAfterDenial,
      applyFinancialTransactionAuthorizationDenial,
      demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState,
      initialFinancialTransactionEnvelopeState]
  · simp [demoFinancialEnvelopeRequest, demoFinancialProcessorAfterDenial,
      applyFinancialTransactionAuthorizationDenial,
      demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState,
      initialFinancialTransactionEnvelopeState,
      initialReplayProtectedFinancialState]

theorem demoFinancialProcessor_success_with_new_id_after_policy_change :
    FinancialTransactionProcessorSuccessStep demoAuthorizationPolicy
      demoHolderLedgerMap DemoLedgerAccount.control 18
      demoFinancialEnvelopeRequest demoFinancialProcessorAfterDenial
      demoFinancialProcessorAfterNewIdSuccess := by
  refine ⟨?_, demoFinancialProcessor_underlying_success_with_new_id, rfl⟩
  simp [demoFinancialProcessorAfterDenial,
    applyFinancialTransactionAuthorizationDenial,
    demoFinancialProcessorInitialState,
    initialFinancialTransactionProcessorState]

theorem demoFinancialProcessor_new_id_success_advances_nonce_to_one :
    demoFinancialProcessorAfterNewIdSuccess.envelope.core.nextNonce
      DemoPrincipal.alice = 1 := by
  have hNext := financialTransactionEnvelopeSuccess_advances_nonce
    demoAuthorizationPolicy demoHolderLedgerMap DemoLedgerAccount.control
    18 demoFinancialEnvelopeRequest
    demoFinancialProcessor_underlying_success_with_new_id
  simpa [demoFinancialEnvelopeRequest] using hNext

theorem demoFinancialProcessor_denial_receipt_persists_after_success :
    demoFinancialProcessorAfterNewIdSuccess.denials 17 =
      some (financialTransactionAuthorizationDenialReceipt
        17 demoFinancialEnvelopeRequest .transferAuthorizationDenied) := by
  have hStored := financialTransactionAuthorizationDenial_stores_receipt
    demoFinancialProcessorDeniedPolicy 17 demoFinancialEnvelopeRequest
    .transferAuthorizationDenied
    demoFinancialProcessor_denial_is_admitted_at_current_nonce
  simpa [demoFinancialProcessorAfterNewIdSuccess] using hStored

theorem demoFinancialProcessor_denial_response_replays_after_nonce_advance :
    cachedFinancialTransactionProcessorResponse
      demoFinancialProcessorAfterNewIdSuccess 17 demoFinancialEnvelopeRequest =
      some (.authorizationRejected
        (financialTransactionAuthorizationDenialReceipt
          17 demoFinancialEnvelopeRequest .transferAuthorizationDenied)) := by
  have hNoSuccess :
      demoFinancialProcessorAfterNewIdSuccess.envelope.receipts 17 = none := by
    simp [demoFinancialProcessorAfterNewIdSuccess,
      applyFinancialTransactionSuccess,
      demoFinancialProcessorAfterDenial,
      applyFinancialTransactionAuthorizationDenial,
      demoFinancialProcessorInitialState,
      initialFinancialTransactionProcessorState,
      initialFinancialTransactionEnvelopeState]
  exact financialTransactionDenialReplay_returns_cached_response
    demoFinancialProcessorAfterNewIdSuccess 17 demoFinancialEnvelopeRequest
    (financialTransactionAuthorizationDenialReceipt
      17 demoFinancialEnvelopeRequest .transferAuthorizationDenied)
    demoFinancialProcessor_denial_receipt_persists_after_success
    rfl rfl hNoSuccess

theorem demoFinancialProcessor_old_denial_nonce_is_now_stale :
    demoFinancialEnvelopeRequest.nonce ≠
      demoFinancialProcessorAfterNewIdSuccess.envelope.core.nextNonce
        DemoPrincipal.alice := by
  rw [demoFinancialProcessor_new_id_success_advances_nonce_to_one]
  simp [demoFinancialEnvelopeRequest]

theorem demoFinancialProcessor_old_denial_remains_exact_replay :
    FinancialTransactionProcessorReplayStep 17 demoFinancialEnvelopeRequest
      demoFinancialProcessorAfterNewIdSuccess
      demoFinancialProcessorAfterNewIdSuccess := by
  right
  exact ⟨
    financialTransactionAuthorizationDenialReceipt
      17 demoFinancialEnvelopeRequest .transferAuthorizationDenied,
    demoFinancialProcessor_denial_receipt_persists_after_success,
    rfl, rfl, rfl⟩

def demoDeniedFinancialProcessorMachine :
    VerifiedStateMachine
      (FinancialTransactionProcessorState Nat DemoPrincipal DemoAccount
        DemoLedgerAccount DemoAsset) :=
  financialTransactionProcessorMachine demoFinancialProcessorDeniedPolicy
    demoHolderLedgerMap DemoLedgerAccount.control demoInitialFinancialState
    demoInitialFinancialState_invariant

theorem demoDeniedFinancialProcessor_initial_reachable :
    Reachable demoDeniedFinancialProcessorMachine
      demoFinancialProcessorInitialState :=
  Reachable.initial rfl

theorem demoDeniedFinancialProcessor_after_denial_reachable :
    Reachable demoDeniedFinancialProcessorMachine
      demoFinancialProcessorAfterDenial :=
  Reachable.step demoDeniedFinancialProcessor_initial_reachable
    (Or.inr (Or.inl ⟨17, demoFinancialEnvelopeRequest,
      .transferAuthorizationDenied,
      demoFinancialProcessor_denial_is_admitted_at_current_nonce⟩))

theorem demoDeniedFinancialProcessor_reachable_invariant :
    FinancialTransactionProcessorInvariant demoHolderLedgerMap
      demoInitialFinancialState.ledger demoFinancialProcessorAfterDenial :=
  financialTransactionProcessorInvariant_of_reachable
    demoFinancialProcessorDeniedPolicy demoHolderLedgerMap
    DemoLedgerAccount.control demoInitialFinancialState
    demoInitialFinancialState_invariant
    demoDeniedFinancialProcessor_after_denial_reachable

end SIRMTests
