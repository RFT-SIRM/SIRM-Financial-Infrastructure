import SIRM.AuthorizedStateMachine
import SIRM.HolderAccountingBridge

/-!
# Authorized Financial State Machine

This module combines the holder-balance projection and signed general ledger
into one state. Every admitted operation updates both projections together.

Issuance and burn require a designated counterpart account outside the
holder-subledger mapping. Its accounting classification is not selected here.
-/

namespace SIRM

/-- The combined holder and general-ledger state. -/
structure FinancialState (Holder LedgerAccount Asset : Type) where
  holdings : HoldingsState Holder Asset
  ledger : Ledger LedgerAccount Asset

/--
The combined financial invariant consists of:
1. valid holder/supply reconciliation; and
2. pointwise agreement between every mapped holder and its GL subledger.
-/
def FinancialInvariant
    {Holder LedgerAccount Asset : Type}
    [Fintype Holder]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (state : FinancialState Holder LedgerAccount Asset) : Prop :=
  HoldingsInvariant state.holdings ∧
    HolderSubledgerAgreement mapping state.holdings state.ledger

/--
The complete financial invariant also records conservation of the aggregate
signed GL balance for every asset relative to an opening ledger.
-/
def FinancialConservationInvariant
    {Holder LedgerAccount Asset : Type}
    [Fintype Holder] [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    (state : FinancialState Holder LedgerAccount Asset) : Prop :=
  FinancialInvariant mapping state ∧
    ∀ asset,
      totalSignedBalance state.ledger asset =
        totalSignedBalance openingLedger asset

/--
An admitted financial transition changes holder balances and the matching
general-ledger journal atomically at the level of this mathematical model.

Transfers use the mapped transfer journal. Issuance and burn additionally
require the counterpart to be unmapped from every holder subledger.
-/
def AuthorizedFinancialStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (before after : FinancialState Holder LedgerAccount Asset) : Prop :=
  (∃ (principal : Principal) (source destination : Holder)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayTransfer before.holdings principal
          source destination asset amount)
      (hAllowed :
        TransferAllowed before.holdings source destination asset amount),
      after =
        { holdings := executeAuthorizedTransfer policy before.holdings
            principal source destination asset amount hAuthorized hAllowed
          ledger := postJournal before.ledger
            (holderTransferJournal mapping source destination asset amount) })
  ∨
  (∃ (principal : Principal) (issuer recipient : Holder)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayIssue before.holdings principal issuer recipient asset amount)
      (_hCounterpart :
        ∀ holder, counterpart ≠ mapping.ledgerAccount holder),
      after =
        { holdings := executeAuthorizedIssue policy before.holdings
            principal issuer recipient asset amount hAuthorized
          ledger := postJournal before.ledger
            (holderIssuanceJournal mapping counterpart recipient asset amount) })
  ∨
  (∃ (principal : Principal) (holder : Holder)
      (asset : Asset) (amount : Nat)
      (hAuthorized :
        policy.mayBurn before.holdings principal holder asset amount)
      (hEnough :
        (amount : Int) ≤ before.holdings.balance holder asset)
      (_hCounterpart :
        ∀ mappedHolder, counterpart ≠ mapping.ledgerAccount mappedHolder),
      after =
        { holdings := executeAuthorizedBurn policy before.holdings
            principal holder asset amount hAuthorized hEnough
          ledger := postJournal before.ledger
            (holderBurnJournal mapping counterpart holder asset amount) })

/--
Every authorized financial transition preserves both holder reconciliation
and mapped holder/GL subledger agreement.
-/
theorem authorizedFinancialStep_preserves_invariant
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    {before after : FinancialState Holder LedgerAccount Asset}
    (hBefore : FinancialInvariant mapping before)
    (hStep : AuthorizedFinancialStep policy mapping counterpart before after) :
    FinancialInvariant mapping after := by
  rcases hStep with hTransfer | hRest
  · rcases hTransfer with
      ⟨principal, source, destination, asset, amount,
        hAuthorized, hAllowed, hEq⟩
    subst after
    constructor
    · exact executeAuthorizedTransfer_preserves_invariant
        policy before.holdings hBefore.1
        principal source destination asset amount hAuthorized hAllowed
    · exact holderSubledgerAgreement_transfer
        mapping before.holdings before.ledger hBefore.2
        source destination asset amount hAllowed
  · rcases hRest with hIssue | hBurn
    · rcases hIssue with
        ⟨principal, issuer, recipient, asset, amount,
          hAuthorized, hCounterpart, hEq⟩
      subst after
      constructor
      · exact executeAuthorizedIssue_preserves_invariant
          policy before.holdings hBefore.1
          principal issuer recipient asset amount hAuthorized
      · exact holderSubledgerAgreement_issue
          mapping before.holdings before.ledger hBefore.2
          counterpart hCounterpart recipient asset amount
    · rcases hBurn with
        ⟨principal, holder, asset, amount,
          hAuthorized, hEnough, hCounterpart, hEq⟩
      subst after
      constructor
      · exact executeAuthorizedBurn_preserves_invariant
          policy before.holdings hBefore.1
          principal holder asset amount hAuthorized hEnough
      · exact holderSubledgerAgreement_burn
          mapping before.holdings before.ledger hBefore.2
          counterpart hCounterpart holder asset amount

/--
A financial machine starts at one state satisfying both invariants and
admits only authorized transitions that update both accounting projections.
-/
def authorizedFinancialMachine
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState) :
    VerifiedStateMachine (FinancialState Holder LedgerAccount Asset) where
  invariant := FinancialInvariant mapping
  initial := fun state => state = initialState
  step := AuthorizedFinancialStep policy mapping counterpart
  initial_safe := by
    intro state hState
    subst state
    exact hInitial
  step_safe := by
    intro before after hBefore hStep
    exact authorizedFinancialStep_preserves_invariant
      policy mapping counterpart hBefore hStep

/--
Every state reachable from a jointly reconciled initial financial state
through authorized transfer, issuance, and burn steps remains reconciled
both in holder balances and in the mapped general ledger.
-/
theorem financialInvariant_of_authorized_reachable
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState)
    {state : FinancialState Holder LedgerAccount Asset}
    (hReachable :
      Reachable
        (authorizedFinancialMachine policy mapping counterpart
          initialState hInitial) state) :
    FinancialInvariant mapping state := by
  exact invariant_of_reachable
    (authorizedFinancialMachine policy mapping counterpart
      initialState hInitial) hReachable


/--
Each authorized financial step preserves the combined holder/GL invariant
and the aggregate signed GL balance relative to the opening ledger.
The conservation conjunct follows from the balanced journal for the step.
-/
theorem authorizedFinancialStep_preserves_conservation
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    {before after : FinancialState Holder LedgerAccount Asset}
    (hBefore : FinancialConservationInvariant mapping openingLedger before)
    (hStep : AuthorizedFinancialStep policy mapping counterpart before after) :
    FinancialConservationInvariant mapping openingLedger after := by
  constructor
  · exact authorizedFinancialStep_preserves_invariant
      policy mapping counterpart hBefore.1 hStep
  · intro queryAsset
    rcases hStep with hTransfer | hRest
    · rcases hTransfer with
        ⟨principal, source, destination, asset, amount,
          hAuthorized, hAllowed, hEq⟩
      subst after
      calc
        totalSignedBalance
            (postJournal before.ledger
              (holderTransferJournal mapping source destination asset amount))
            queryAsset =
          totalSignedBalance before.ledger queryAsset :=
            totalSignedBalance_postJournal before.ledger
              (holderTransferJournal mapping source destination asset amount)
              queryAsset
        _ = totalSignedBalance openingLedger queryAsset :=
          hBefore.2 queryAsset
    · rcases hRest with hIssue | hBurn
      · rcases hIssue with
          ⟨principal, issuer, recipient, asset, amount,
            hAuthorized, hCounterpart, hEq⟩
        subst after
        calc
          totalSignedBalance
              (postJournal before.ledger
                (holderIssuanceJournal mapping counterpart recipient asset amount))
              queryAsset =
            totalSignedBalance before.ledger queryAsset :=
              totalSignedBalance_postJournal before.ledger
                (holderIssuanceJournal mapping counterpart recipient asset amount)
                queryAsset
          _ = totalSignedBalance openingLedger queryAsset :=
            hBefore.2 queryAsset
      · rcases hBurn with
          ⟨principal, holder, asset, amount,
            hAuthorized, hEnough, hCounterpart, hEq⟩
        subst after
        calc
          totalSignedBalance
              (postJournal before.ledger
                (holderBurnJournal mapping counterpart holder asset amount))
              queryAsset =
            totalSignedBalance before.ledger queryAsset :=
              totalSignedBalance_postJournal before.ledger
                (holderBurnJournal mapping counterpart holder asset amount)
                queryAsset
          _ = totalSignedBalance openingLedger queryAsset :=
            hBefore.2 queryAsset

/--
The stronger financial machine starts with a reconciled holder/GL state
and preserves aggregate signed-ledger totals at every admitted transition.
-/
def authorizedFinancialMachineWithConservation
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState) :
    VerifiedStateMachine (FinancialState Holder LedgerAccount Asset) where
  invariant := FinancialConservationInvariant mapping initialState.ledger
  initial := fun state => state = initialState
  step := AuthorizedFinancialStep policy mapping counterpart
  initial_safe := by
    intro state hState
    subst state
    exact ⟨hInitial, by intro asset; rfl⟩
  step_safe := by
    intro before after hBefore hStep
    exact authorizedFinancialStep_preserves_conservation
      policy mapping counterpart initialState.ledger hBefore hStep

/--
Every state reachable through the authorized financial machine preserves
holder reconciliation, mapped subledger agreement, and aggregate GL balance.
-/
theorem financialConservationInvariant_of_authorized_reachable
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (policy : AuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (counterpart : LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState)
    {state : FinancialState Holder LedgerAccount Asset}
    (hReachable :
      Reachable
        (authorizedFinancialMachineWithConservation
          policy mapping counterpart initialState hInitial) state) :
    FinancialConservationInvariant mapping initialState.ledger state := by
  exact invariant_of_reachable
    (authorizedFinancialMachineWithConservation
      policy mapping counterpart initialState hInitial) hReachable

end SIRM
