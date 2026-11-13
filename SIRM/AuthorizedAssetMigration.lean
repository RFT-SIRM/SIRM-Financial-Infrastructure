import SIRM.AssetMigration
import SIRM.AccountControl
import SIRM.AuthorizedFinancialMachine

/-!
# Authorized Atomic Cross-Network Asset Migration

A migration is one state transition that burns source base units, issues the
exact target amount released by the route's residual accumulator, posts both
balanced journal entries, and advances the residual claim subledger.

The migration partition is fixed to one route, one source holder, and one
destination recipient. It also carries proofs that the two accounts belong
to the corresponding endpoint networks. This prevents residuals from being
silently pooled across routes or account pairs.

The residual is a separate exact claim subledger. This module does not post a
fractional residual to the integer-valued general ledger, and does not claim
that the residual is a legally enforceable or externally backed liability.
-/

namespace SIRM

/--
A migration claim partition fixes the exact route and the source/beneficiary
account pair. The network proofs ensure that the accounts belong to the
respective endpoint networks.
-/
structure AuthorizedAssetMigrationPartition
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    (registry : AssetRegistry accountCount assetCount accounts) where
  route : AssetMigrationRoute registry
  sourceHolder : AccountId accountCount
  recipient : AccountId accountCount
  source_holder_on_source_network :
    (accounts.metadata sourceHolder).network =
      (registry.metadata route.sourceAsset).network
  recipient_on_destination_network :
    (accounts.metadata recipient).network =
      (registry.metadata route.destinationAsset).network

namespace AssetMigrationDustState

/-- Target base units released by this accrual, including carried dust. -/
def targetBaseUnitsReleased
    {rate : AssetMigrationRate}
    {Partition : Type}
    {partition : Partition}
    (state : AssetMigrationDustState rate Partition partition)
    (sourceBaseUnits : Nat) : Nat :=
  (state.dustNumerator + sourceBaseUnits * rate.numerator) /
    rate.denominator

@[simp]
theorem addSource_totalSourceBaseUnits
    {rate : AssetMigrationRate}
    {Partition : Type}
    {partition : Partition}
    (state : AssetMigrationDustState rate Partition partition)
    (sourceBaseUnits : Nat) :
    (state.addSource sourceBaseUnits).totalSourceBaseUnits =
      state.totalSourceBaseUnits + sourceBaseUnits := by
  rfl

@[simp]
theorem addSource_totalTargetBaseUnits
    {rate : AssetMigrationRate}
    {Partition : Type}
    {partition : Partition}
    (state : AssetMigrationDustState rate Partition partition)
    (sourceBaseUnits : Nat) :
    (state.addSource sourceBaseUnits).totalTargetBaseUnits =
      state.totalTargetBaseUnits +
        state.targetBaseUnitsReleased sourceBaseUnits := by
  rfl

end AssetMigrationDustState

/--
The state of one route/source/recipient migration stream. Both the ordinary
financial projections and the exact fractional claim accumulator are part
of the same state value.
-/
structure AuthorizedAssetMigrationState
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (partition : AuthorizedAssetMigrationPartition registry)
    (LedgerAccount : Type) where
  financial : FinancialState
    (AccountId accountCount) LedgerAccount (AssetId assetCount)
  dust : AssetMigrationDustState
    partition.route.rate
    (AuthorizedAssetMigrationPartition registry)
    partition

/-- Initial migration state: the supplied financial state and an empty claim accumulator. -/
def initialAuthorizedAssetMigrationState
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    (partition : AuthorizedAssetMigrationPartition registry)
    {LedgerAccount : Type}
    (initialFinancial : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount)) :
    AuthorizedAssetMigrationState partition LedgerAccount :=
  { financial := initialFinancial
    dust := AssetMigrationDustState.empty partition.route.rate partition }

/--
Apply the two-sided migration update as one pure state transformer. The
source burn, target issuance, their two asset-specific balanced journals,
and the carried residual are returned together; there is no intermediate
machine state containing only one side of the migration.
-/
def applyAuthorizedAssetMigration
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (partition : AuthorizedAssetMigrationPartition registry)
    (before : AuthorizedAssetMigrationState partition LedgerAccount)
    (sourceAmount : Nat) :
    AuthorizedAssetMigrationState partition LedgerAccount := by
  let targetAmount := before.dust.targetBaseUnitsReleased sourceAmount
  exact
    { financial :=
        { holdings :=
            issueToHolder
              (burnFromHolder before.financial.holdings
                partition.sourceHolder partition.route.sourceAsset sourceAmount)
              partition.recipient partition.route.destinationAsset targetAmount
          ledger :=
            postJournal
              (postJournal before.financial.ledger
                (holderBurnJournal mapping counterpart partition.sourceHolder
                  partition.route.sourceAsset sourceAmount))
              (holderIssuanceJournal mapping counterpart partition.recipient
                partition.route.destinationAsset targetAmount) }
      dust := before.dust.addSource sourceAmount }

/--
The combined holder/ledger financial invariant is preserved by the paired
burn-and-issue update, assuming the source holder is sufficiently funded and
the clearing counterpart is outside every holder subledger.
-/
theorem applyAuthorizedAssetMigration_preserves_financial_conservation
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (before : AuthorizedAssetMigrationState partition LedgerAccount)
    (sourceAmount : Nat)
    (openingLedger : Ledger LedgerAccount (AssetId assetCount))
    (hBefore : FinancialConservationInvariant mapping openingLedger before.financial)
    (hEnough : (sourceAmount : Int) ≤
      before.financial.holdings.balance partition.sourceHolder
        partition.route.sourceAsset) :
    FinancialConservationInvariant mapping openingLedger
      (applyAuthorizedAssetMigration mapping counterpart partition
        before sourceAmount).financial := by
  let targetAmount := before.dust.targetBaseUnitsReleased sourceAmount
  let burnedHoldings :=
    burnFromHolder before.financial.holdings partition.sourceHolder
      partition.route.sourceAsset sourceAmount
  let burnedLedger :=
    postJournal before.financial.ledger
      (holderBurnJournal mapping counterpart partition.sourceHolder
        partition.route.sourceAsset sourceAmount)
  have hBurnedHoldings : HoldingsInvariant burnedHoldings := by
    exact burnFromHolder_preserves_invariant
      before.financial.holdings hBefore.1.1
      partition.sourceHolder partition.route.sourceAsset sourceAmount hEnough
  have hFinalHoldings :
      HoldingsInvariant
        (issueToHolder burnedHoldings partition.recipient
          partition.route.destinationAsset targetAmount) := by
    exact issueToHolder_preserves_invariant burnedHoldings hBurnedHoldings
      partition.recipient partition.route.destinationAsset targetAmount
  have hBurnedAgreement :
      HolderSubledgerAgreement mapping burnedHoldings burnedLedger := by
    exact holderSubledgerAgreement_burn
      mapping before.financial.holdings before.financial.ledger hBefore.1.2
      counterpart hCounterpart partition.sourceHolder
      partition.route.sourceAsset sourceAmount
  have hFinalAgreement :
      HolderSubledgerAgreement mapping
        (issueToHolder burnedHoldings partition.recipient
          partition.route.destinationAsset targetAmount)
        (postJournal burnedLedger
          (holderIssuanceJournal mapping counterpart partition.recipient
            partition.route.destinationAsset targetAmount)) := by
    exact holderSubledgerAgreement_issue
      mapping burnedHoldings burnedLedger hBurnedAgreement
      counterpart hCounterpart partition.recipient
      partition.route.destinationAsset targetAmount
  have hTotal : ∀ asset,
      totalSignedBalance
        (postJournal burnedLedger
          (holderIssuanceJournal mapping counterpart partition.recipient
            partition.route.destinationAsset targetAmount)) asset =
      totalSignedBalance openingLedger asset := by
    intro asset
    calc
      totalSignedBalance
          (postJournal burnedLedger
            (holderIssuanceJournal mapping counterpart partition.recipient
              partition.route.destinationAsset targetAmount)) asset =
        totalSignedBalance burnedLedger asset :=
          totalSignedBalance_postJournal burnedLedger
            (holderIssuanceJournal mapping counterpart partition.recipient
              partition.route.destinationAsset targetAmount) asset
      _ = totalSignedBalance before.financial.ledger asset :=
        totalSignedBalance_postJournal before.financial.ledger
          (holderBurnJournal mapping counterpart partition.sourceHolder
            partition.route.sourceAsset sourceAmount) asset
      _ = totalSignedBalance openingLedger asset := hBefore.2 asset
  constructor
  · constructor
    · simpa [applyAuthorizedAssetMigration, targetAmount, burnedHoldings] using
        hFinalHoldings
    · simpa [applyAuthorizedAssetMigration, targetAmount,
        burnedHoldings, burnedLedger] using hFinalAgreement
  · intro asset
    simpa [applyAuthorizedAssetMigration, targetAmount, burnedLedger] using
      hTotal asset

/--
One authorized migration step. A single principal must have source-holder
control plus the exact source burn grant, and destination-issuer control
plus the exact issue grant for the target amount actually released by dust.
Both assets and issuers, both endpoint accounts, and the route networks are
checked before the paired state update is admitted.
-/
def AuthorizedAssetMigrationStep
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal
      (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (_hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal : Principal)
    (sourceAmount : Nat)
    (before after : AuthorizedAssetMigrationState partition LedgerAccount) : Prop :=
  0 < sourceAmount ∧
  AccountRegistry.isActive accounts partition.sourceHolder ∧
  AccountRegistry.isActive accounts partition.recipient ∧
  partition.route.endpointsEnabled ∧
  (toControlledAuthorizationPolicy control authority).mayBurn
    before.financial.holdings principal partition.sourceHolder
      partition.route.sourceAsset sourceAmount ∧
  (toControlledAuthorizationPolicy control authority).mayIssue
    before.financial.holdings principal
      (registry.metadata partition.route.destinationAsset).issuer
      partition.recipient partition.route.destinationAsset
      (before.dust.targetBaseUnitsReleased sourceAmount) ∧
  (sourceAmount : Int) ≤
    before.financial.holdings.balance partition.sourceHolder
      partition.route.sourceAsset ∧
  after = applyAuthorizedAssetMigration mapping counterpart partition
    before sourceAmount

/--
The invariant includes the full holder/GL conservation result and the exact
scaled-value equation carried by the route/source/recipient dust subledger.
-/
def AuthorizedAssetMigrationInvariant
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (openingLedger : Ledger LedgerAccount (AssetId assetCount))
    {partition : AuthorizedAssetMigrationPartition registry}
    (state : AuthorizedAssetMigrationState partition LedgerAccount) : Prop :=
  FinancialConservationInvariant mapping openingLedger state.financial ∧
    state.dust.totalSourceBaseUnits * partition.route.rate.numerator =
      state.dust.totalTargetBaseUnits * partition.route.rate.denominator +
        state.dust.dustNumerator

theorem authorizedAssetMigrationStep_preserves_invariant
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal
      (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (principal : Principal)
    (sourceAmount : Nat)
    {before after : AuthorizedAssetMigrationState partition LedgerAccount}
    (openingLedger : Ledger LedgerAccount (AssetId assetCount))
    (hBefore : AuthorizedAssetMigrationInvariant mapping openingLedger before)
    (hStep : AuthorizedAssetMigrationStep control authority mapping
      counterpart hCounterpart partition principal sourceAmount before after) :
    AuthorizedAssetMigrationInvariant mapping openingLedger after := by
  rcases hStep with
    ⟨_hPositive, _hSourceActive, _hRecipientActive, _hRouteEnabled,
      _hBurnAuthorized, _hIssueAuthorized, hEnough, rfl⟩
  exact ⟨
    applyAuthorizedAssetMigration_preserves_financial_conservation
      mapping counterpart hCounterpart partition before sourceAmount
      openingLedger hBefore.1 hEnough,
    (before.dust.addSource sourceAmount).scaled_conservation
  ⟩

def authorizedAssetMigrationMachine
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal
      (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (initialFinancial : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialFinancial) :
    VerifiedStateMachine (AuthorizedAssetMigrationState partition LedgerAccount) :=
  { invariant := AuthorizedAssetMigrationInvariant mapping initialFinancial.ledger
    initial := fun state =>
      state = initialAuthorizedAssetMigrationState partition initialFinancial
    step := fun before after =>
      ∃ principal sourceAmount,
        AuthorizedAssetMigrationStep control authority mapping counterpart
          hCounterpart partition principal sourceAmount before after
    initial_safe := by
      intro state hState
      cases hState
      exact ⟨⟨hInitial, by intro asset; rfl⟩,
        (AssetMigrationDustState.empty partition.route.rate partition).scaled_conservation⟩
    step_safe := by
      intro before after hBefore hStep
      rcases hStep with ⟨principal, sourceAmount, hStep⟩
      exact authorizedAssetMigrationStep_preserves_invariant
        control authority mapping counterpart hCounterpart partition
        principal sourceAmount initialFinancial.ledger hBefore hStep }

theorem authorizedAssetMigrationInvariant_of_reachable
    {Principal : Type}
    {accountCount assetCount : Nat}
    {accounts : AccountRegistry accountCount}
    {registry : AssetRegistry accountCount assetCount accounts}
    {LedgerAccount : Type}
    [Fintype LedgerAccount] [DecidableEq LedgerAccount]
    [DecidableEq (AccountId accountCount)]
    [DecidableEq (AssetId assetCount)]
    (control : AccountControlRegistry Principal (AccountId accountCount))
    (authority : AuthorityRegistry Principal
      (AccountId accountCount) (AssetId assetCount))
    (mapping : HolderLedgerMap (AccountId accountCount) LedgerAccount)
    (counterpart : LedgerAccount)
    (hCounterpart : ∀ holder : AccountId accountCount,
      counterpart ≠ mapping.ledgerAccount holder)
    (partition : AuthorizedAssetMigrationPartition registry)
    (initialFinancial : FinancialState
      (AccountId accountCount) LedgerAccount (AssetId assetCount))
    (hInitial : FinancialInvariant mapping initialFinancial)
    {state : AuthorizedAssetMigrationState partition LedgerAccount}
    (hReachable : Reachable
      (authorizedAssetMigrationMachine control authority mapping counterpart
        hCounterpart partition initialFinancial hInitial) state) :
    AuthorizedAssetMigrationInvariant mapping initialFinancial.ledger state := by
  exact invariant_of_reachable
    (authorizedAssetMigrationMachine control authority mapping counterpart
      hCounterpart partition initialFinancial hInitial) hReachable

end SIRM
