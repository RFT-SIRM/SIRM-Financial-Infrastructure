import SIRM.AuthorizedFinancialMachine

/-!
# Authorized Fee Accounting

A fee transfer is one abstract financial-state transition with three explicit
holder roles: payer, beneficiary, and fee collector. The payer is debited the
gross amount; the beneficiary receives the net amount; the collector receives
the fee. The fee collector is a member of the holder universe in this first
model, so fees are transfers of already-issued units, not burns or new issuance.

The transfer permission and fee permission are independent policy witnesses.
This module specifies exact integer base-unit mechanics only; it does not
select a tariff, percentage, rounding policy, or production revenue account.
-/ 

namespace SIRM

/-- A policy that separately authorizes a fee for an exact transfer request. -/
structure FeeAuthorizationPolicy (Principal Holder Asset : Type) where
  mayChargeFee :
    HoldingsState Holder Asset → Principal →
      Holder → Holder → Holder → Asset → Nat → Nat → Prop

/-- Fee accounting requires a fee no larger than the gross amount and a funded payer. -/
def FeeTransferAllowed {Holder Asset : Type}
    (state : HoldingsState Holder Asset)
    (sender _recipient _feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat) : Prop :=
  feeAmount ≤ grossAmount ∧
    (grossAmount : Int) ≤ state.balance sender asset

/-- The beneficiary receives the gross amount less the explicit fee. -/
def feeTransferNetAmount (grossAmount feeAmount : Nat) : Nat :=
  grossAmount - feeAmount

/-- Exact decomposition of gross value into net value and fee. -/
theorem feeTransferNetAmount_add_fee
    (grossAmount feeAmount : Nat)
    (hFee : feeAmount ≤ grossAmount) :
    feeTransferNetAmount grossAmount feeAmount + feeAmount = grossAmount := by
  exact Nat.sub_add_cancel hFee

/--
The net leg is funded because its amount cannot exceed the gross amount.
The gross funding condition remains mandatory even when roles coincide.
-/
theorem feeTransfer_net_leg_allowed
    {Holder Asset : Type}
    (state : HoldingsState Holder Asset)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat)
    (hAllowed :
      FeeTransferAllowed state sender recipient feeCollector
        asset grossAmount feeAmount) :
    TransferAllowed state sender recipient asset
      (feeTransferNetAmount grossAmount feeAmount) := by
  rcases hAllowed with ⟨_, hGross⟩
  apply Or.inr
  have hNet : feeTransferNetAmount grossAmount feeAmount ≤ grossAmount := by
    exact Nat.sub_le _ _
  exact le_trans (by exact_mod_cast hNet) hGross

/--
After the net leg, the payer has enough for the fee leg. If payer and
beneficiary coincide, the net leg is a no-op; otherwise the payer has lost
exactly the net amount, and net + fee is the funded gross amount.
-/
theorem feeTransfer_fee_leg_allowed
    {Holder Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    (state : HoldingsState Holder Asset)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat)
    (hAllowed :
      FeeTransferAllowed state sender recipient feeCollector
        asset grossAmount feeAmount) :
    TransferAllowed
      (transferBetweenHolders state sender recipient asset
        (feeTransferNetAmount grossAmount feeAmount))
      sender feeCollector asset feeAmount := by
  rcases hAllowed with ⟨hFee, hGross⟩
  by_cases hSelf : sender = feeCollector
  · exact Or.inl hSelf
  · apply Or.inr
    by_cases hSenderRecipient : sender = recipient
    · subst recipient
      simpa [transferBetweenHolders] using
        (le_trans (by exact_mod_cast hFee : (feeAmount : Int) ≤ (grossAmount : Int))
          hGross)
    · have hAfterNet :
        (transferBetweenHolders state sender recipient asset
          (feeTransferNetAmount grossAmount feeAmount)).balance sender asset =
          state.balance sender asset -
            (feeTransferNetAmount grossAmount feeAmount : Int) := by
        simp [transferBetweenHolders, hSenderRecipient]
      rw [hAfterNet]
      have hSplit :
          (feeTransferNetAmount grossAmount feeAmount : Int) +
              (feeAmount : Int) = (grossAmount : Int) := by
        exact_mod_cast feeTransferNetAmount_add_fee grossAmount feeAmount hFee
      omega

/--
Apply the net transfer and fee transfer in sequence. The function returns one
final holder state; no intermediate state is admitted by the fee-step relation.
-/
def feeTransferHoldings
    {Holder Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    (state : HoldingsState Holder Asset)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat) :
    HoldingsState Holder Asset :=
  transferBetweenHolders
    (transferBetweenHolders state sender recipient asset
      (feeTransferNetAmount grossAmount feeAmount))
    sender feeCollector asset feeAmount

/-- A valid fee transfer preserves holder/supply reconciliation. -/
theorem feeTransferHoldings_preserves_invariant
    {Holder Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    (state : HoldingsState Holder Asset)
    (hInvariant : HoldingsInvariant state)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat)
    (hAllowed :
      FeeTransferAllowed state sender recipient feeCollector
        asset grossAmount feeAmount) :
    HoldingsInvariant
      (feeTransferHoldings state sender recipient feeCollector
        asset grossAmount feeAmount) := by
  unfold feeTransferHoldings
  exact transferBetweenHolders_preserves_invariant
    (transferBetweenHolders state sender recipient asset
      (feeTransferNetAmount grossAmount feeAmount))
    (transferBetweenHolders_preserves_invariant state hInvariant
      sender recipient asset (feeTransferNetAmount grossAmount feeAmount)
      (feeTransfer_net_leg_allowed state sender recipient feeCollector
        asset grossAmount feeAmount hAllowed))
    sender feeCollector asset feeAmount
    (feeTransfer_fee_leg_allowed state sender recipient feeCollector
      asset grossAmount feeAmount hAllowed)

/--
One fee journal is the sum of two ordinary balanced holder-transfer journals:
sender → beneficiary for the net amount and sender → collector for the fee.
Their combined debit is exactly the gross amount by the fee decomposition.
-/
def feeTransferJournal
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat) :
    JournalEntry LedgerAccount Asset where
  posting := fun account currentAsset =>
    (holderTransferJournal mapping sender recipient asset
      (feeTransferNetAmount grossAmount feeAmount)).posting account currentAsset +
    (holderTransferJournal mapping sender feeCollector asset feeAmount).posting
      account currentAsset
  balanced := by
    intro currentAsset
    rw [Finset.sum_add_distrib]
    rw [holderTransferJournal_balanced mapping sender recipient asset
      currentAsset (feeTransferNetAmount grossAmount feeAmount)]
    rw [holderTransferJournal_balanced mapping sender feeCollector asset
      currentAsset feeAmount]
    simp

/--
Posting the combined fee journal is equal to applying its two balanced legs
inside one final ledger value. This algebraic identity connects the compact
journal to the sequential holder/subledger preservation proof.
-/
theorem postJournal_feeTransferJournal_eq
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (ledger : Ledger LedgerAccount Asset)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat) :
    postJournal ledger
        (feeTransferJournal mapping sender recipient feeCollector
          asset grossAmount feeAmount) =
      postJournal
        (postJournal ledger
          (holderTransferJournal mapping sender recipient asset
            (feeTransferNetAmount grossAmount feeAmount)))
        (holderTransferJournal mapping sender feeCollector asset feeAmount) := by
  change
    Ledger.mk (fun account currentAsset =>
      ledger.balance account currentAsset +
        (feeTransferJournal mapping sender recipient feeCollector
          asset grossAmount feeAmount).posting account currentAsset) =
    Ledger.mk (fun account currentAsset =>
      (ledger.balance account currentAsset +
        (holderTransferJournal mapping sender recipient asset
          (feeTransferNetAmount grossAmount feeAmount)).posting
            account currentAsset) +
        (holderTransferJournal mapping sender feeCollector asset feeAmount).posting
          account currentAsset)
  apply congrArg Ledger.mk
  funext account currentAsset
  simp [feeTransferJournal]
  ring

/-- The combined journal preserves the holder-to-subledger agreement. -/
theorem holderSubledgerAgreement_feeTransfer
    {Holder LedgerAccount Asset : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount] [DecidableEq Asset]
    [DecidableEq Holder]
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (holdings : HoldingsState Holder Asset)
    (ledger : Ledger LedgerAccount Asset)
    (hAgreement : HolderSubledgerAgreement mapping holdings ledger)
    (sender recipient feeCollector : Holder)
    (asset : Asset) (grossAmount feeAmount : Nat)
    (hAllowed :
      FeeTransferAllowed holdings sender recipient feeCollector
        asset grossAmount feeAmount) :
    HolderSubledgerAgreement mapping
      (feeTransferHoldings holdings sender recipient feeCollector
        asset grossAmount feeAmount)
      (postJournal ledger
        (feeTransferJournal mapping sender recipient feeCollector
          asset grossAmount feeAmount)) := by
  have hNetAllowed :=
    feeTransfer_net_leg_allowed holdings sender recipient feeCollector
      asset grossAmount feeAmount hAllowed
  have hFeeAllowed :=
    feeTransfer_fee_leg_allowed holdings sender recipient feeCollector
      asset grossAmount feeAmount hAllowed
  have hAfterNet :=
    holderSubledgerAgreement_transfer mapping holdings ledger hAgreement
      sender recipient asset
      (feeTransferNetAmount grossAmount feeAmount) hNetAllowed
  have hAfterFee :=
    holderSubledgerAgreement_transfer mapping
      (transferBetweenHolders holdings sender recipient asset
        (feeTransferNetAmount grossAmount feeAmount))
      (postJournal ledger
        (holderTransferJournal mapping sender recipient asset
          (feeTransferNetAmount grossAmount feeAmount)))
      hAfterNet sender feeCollector asset feeAmount hFeeAllowed
  rw [postJournal_feeTransferJournal_eq]
  exact hAfterFee

/--
An authorized fee transfer requires both the ordinary transfer permission
for the gross amount and a separate fee-policy witness for the exact fee and
collector. The funding and fee-bound proof is also explicit.
-/
def FeeTransferStep
    {Principal Holder LedgerAccount Asset : Type}
    [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (feePolicy : FeeAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (before after : FinancialState Holder LedgerAccount Asset) : Prop :=
  ∃ (principal : Principal) (sender recipient feeCollector : Holder)
      (asset : Asset) (grossAmount feeAmount : Nat)
      (_hTransfer :
        transferPolicy.mayTransfer before.holdings principal
          sender recipient asset grossAmount)
      (_hFee :
        feePolicy.mayChargeFee before.holdings principal
          sender recipient feeCollector asset grossAmount feeAmount)
      (_hAllowed :
        FeeTransferAllowed before.holdings sender recipient feeCollector
          asset grossAmount feeAmount),
      after =
        { holdings := feeTransferHoldings before.holdings sender recipient
            feeCollector asset grossAmount feeAmount
          ledger := postJournal before.ledger
            (feeTransferJournal mapping sender recipient feeCollector
              asset grossAmount feeAmount) }

/-- Every admitted fee transfer preserves holder reconciliation and GL agreement. -/
theorem feeTransferStep_preserves_invariant
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (feePolicy : FeeAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    {before after : FinancialState Holder LedgerAccount Asset}
    (hBefore : FinancialInvariant mapping before)
    (hStep : FeeTransferStep transferPolicy feePolicy mapping before after) :
    FinancialInvariant mapping after := by
  rcases hStep with
    ⟨principal, sender, recipient, feeCollector, asset, grossAmount, feeAmount,
      hTransfer, hFee, hAllowed, hEq⟩
  subst after
  exact
    ⟨feeTransferHoldings_preserves_invariant before.holdings hBefore.1
        sender recipient feeCollector asset grossAmount feeAmount hAllowed,
      holderSubledgerAgreement_feeTransfer mapping before.holdings before.ledger
        hBefore.2 sender recipient feeCollector asset grossAmount feeAmount hAllowed⟩

/--
The full fee transition preserves holder/supply reconciliation, mapped
subledger agreement, and the aggregate signed GL total for every asset.
-/
theorem feeTransferStep_preserves_conservation
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (feePolicy : FeeAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (openingLedger : Ledger LedgerAccount Asset)
    {before after : FinancialState Holder LedgerAccount Asset}
    (hBefore :
      FinancialConservationInvariant mapping openingLedger before)
    (hStep : FeeTransferStep transferPolicy feePolicy mapping before after) :
    FinancialConservationInvariant mapping openingLedger after := by
  rcases hStep with
    ⟨principal, sender, recipient, feeCollector, asset, grossAmount, feeAmount,
      hTransfer, hFee, hAllowed, hEq⟩
  subst after
  constructor
  · exact feeTransferStep_preserves_invariant transferPolicy feePolicy
      mapping hBefore.1
      ⟨principal, sender, recipient, feeCollector, asset, grossAmount, feeAmount,
        hTransfer, hFee, hAllowed, rfl⟩
  · intro queryAsset
    calc
      totalSignedBalance
          (postJournal before.ledger
            (feeTransferJournal mapping sender recipient feeCollector
              asset grossAmount feeAmount)) queryAsset =
        totalSignedBalance before.ledger queryAsset :=
          totalSignedBalance_postJournal before.ledger
            (feeTransferJournal mapping sender recipient feeCollector
              asset grossAmount feeAmount) queryAsset
      _ = totalSignedBalance openingLedger queryAsset :=
        hBefore.2 queryAsset

/-- Verified machine whose only transitions are separately authorized fee transfers. -/
def feeTransferMachine
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (feePolicy : FeeAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState) :
    VerifiedStateMachine (FinancialState Holder LedgerAccount Asset) where
  invariant := FinancialConservationInvariant mapping initialState.ledger
  initial := fun state => state = initialState
  step := FeeTransferStep transferPolicy feePolicy mapping
  initial_safe := by
    intro state hState
    subst state
    exact ⟨hInitial, by intro asset; rfl⟩
  step_safe := by
    intro before after hBefore hStep
    exact feeTransferStep_preserves_conservation
      transferPolicy feePolicy mapping initialState.ledger hBefore hStep

/-- Every state reachable through authorized fee transfers retains the complete invariant. -/
theorem feeTransferInvariant_of_reachable
    {Principal Holder LedgerAccount Asset : Type}
    [Fintype Holder] [DecidableEq Holder] [DecidableEq Asset]
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (transferPolicy : AuthorizationPolicy Principal Holder Asset)
    (feePolicy : FeeAuthorizationPolicy Principal Holder Asset)
    (mapping : HolderLedgerMap Holder LedgerAccount)
    (initialState : FinancialState Holder LedgerAccount Asset)
    (hInitial : FinancialInvariant mapping initialState)
    {state : FinancialState Holder LedgerAccount Asset}
    (hReachable :
      Reachable (feeTransferMachine transferPolicy feePolicy mapping
        initialState hInitial) state) :
    FinancialConservationInvariant mapping initialState.ledger state := by
  exact invariant_of_reachable
    (feeTransferMachine transferPolicy feePolicy mapping initialState hInitial)
    hReachable

end SIRM
