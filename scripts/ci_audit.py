from pathlib import Path
from urllib.parse import urlsplit, unquote
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

def load(path):
    p = ROOT / path
    if not p.is_file():
        raise AssertionError(f"required file missing: {path}")
    return p.read_text()

def need(condition, message):
    if not condition:
        raise AssertionError(message)

def no_proof_holes():
    files = list((ROOT / "SIRM").rglob("*.lean")) + [ROOT / "SIRMTests.lean"]
    hits = []
    for path in files:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if re.match(r"^\s*(sorry|admit)\b", line):
                hits.append(f"{path.relative_to(ROOT)}:{number}: {line.strip()}")
    need(not hits, "proof placeholders found:\n" + "\n".join(hits))

def issue_api_shape():
    src = load("SIRM/Authorization.lean")
    body = src.split("  mayIssue :", 1)[1].split("  mayBurn :", 1)[0]
    need("Account → Account → Asset → Nat → Prop" in body,
         "mayIssue must take issuer and recipient accounts")
    need("policy.mayIssue state principal issuer recipient asset amount" in src,
         "authorized issue witness does not bind issuer and recipient")

def issuer_recipient_scope():
    src = load("SIRM/AuthorityRegistry.lean")
    need("| issue (issuer recipient : Account)" in src,
         "AuthorityScope.issue must bind issuer and recipient")

def registry_issue_adapter():
    src = load("SIRM/AuthorityRegistry.lean")
    need("mayIssue := fun _ principal issuer recipient asset amount =>" in src,
         "registry adapter is missing issuer/recipient arguments")
    need("(.issue issuer recipient) asset amount" in src,
         "registry adapter does not bind the exact issuer/recipient pair")

def finite_control_relation():
    src = load("SIRM/AccountControl.lean")
    need("structure AccountControlRegistry (Principal Account : Type)" in src,
         "account-control registry declaration missing")
    need("entries : List (Principal × Account)" in src,
         "account control must be represented by a finite principal/account relation")
    need("(principal, account) ∈ registry.entries" in src,
         "controls must be defined by relation membership")

def transfer_dual_gate():
    src = load("SIRM/AccountControl.lean")
    body = src.split("  mayTransfer := ", 1)[1].split("  mayIssue := ", 1)[0]
    need("controls control principal source" in body,
         "transfer does not require control of its source")
    need("AuthorityRegistry.allows authority principal" in body and
         "(.transfer source destination)" in body,
         "transfer does not require the exact directional grant")

def issue_dual_gate():
    src = load("SIRM/AccountControl.lean")
    body = src.split("  mayIssue := ", 1)[1].split("  mayBurn := ", 1)[0]
    need("controls control principal issuer" in body,
         "issuance does not require control of issuer")
    need("AuthorityRegistry.allows authority principal" in body and
         "(.issue issuer recipient)" in body,
         "issuance does not require the exact issuer/recipient grant")

def burn_dual_gate():
    src = load("SIRM/AccountControl.lean")
    body = src.split("  mayBurn := ", 1)[1].split("\n\n@[simp]", 1)[0]
    need("controls control principal holder" in body,
         "burn does not require control of holder")
    need("AuthorityRegistry.allows authority principal" in body and
         "(.burn holder)" in body,
         "burn does not require the exact holder grant")

def issue_credits_recipient():
    auth = load("SIRM/Authorization.lean")
    financial = load("SIRM/AuthorizedFinancialMachine.lean")
    need("issueToHolder state recipient asset amount" in auth,
         "issuance must credit the recipient")
    need("holderIssuanceJournal mapping counterpart recipient asset amount" in financial,
         "issuance journal must post to recipient")
    need("issueToHolder state issuer asset amount" not in auth,
         "issuer must not be substituted for recipient in the holdings transition")

def holder_machine_issuer():
    src = load("SIRM/AuthorizedStateMachine.lean")
    need("(∃ (principal : Principal) (issuer recipient : Account)" in src,
         "holder machine issue branch is missing issuer")
    need("policy.mayIssue before principal issuer recipient asset amount" in src,
         "holder machine authorization witness omits issuer/recipient")
    need("executeAuthorizedIssue policy before principal issuer recipient" in src,
         "holder machine transition omits issuer/recipient")

def financial_machine_issuer():
    src = load("SIRM/AuthorizedFinancialMachine.lean")
    need("(∃ (principal : Principal) (issuer recipient : Holder)" in src,
         "financial issue branch is missing issuer")
    need("policy.mayIssue before.holdings principal issuer recipient asset amount" in src,
         "financial authorization witness omits issuer/recipient")
    need("executeAuthorizedIssue policy before.holdings\n            principal issuer recipient" in src,
         "financial holdings transition omits issuer/recipient")
    need("⟨principal, issuer, recipient, asset, amount," in src,
         "financial invariant/conservation proof does not destruct issuer witness")

def deny_grant_without_control():
    src = load("SIRMTests.lean")
    need("theorem registryGrantWithoutAccountControlIsDenied" in src,
         "missing regression theorem for grant without control")
    body = src.split("theorem registryGrantWithoutAccountControlIsDenied", 1)[1]
    body = body.split("theorem registryAccountControlWithoutGrantIsDenied", 1)[0]
    need("demoNoControlRegistryPolicy" in body and "demoEmptyAccountControlRegistry" in src,
         "no-control negative scenario is not wired to the empty control registry")

def deny_control_without_grant():
    src = load("SIRMTests.lean")
    need("theorem registryAccountControlWithoutGrantIsDenied" in src,
         "missing regression theorem for control without grant")
    body = src.split("theorem registryAccountControlWithoutGrantIsDenied", 1)[1]
    body = body.split("theorem treasuryDoesNotControlAlice", 1)[0]
    need("demoControlledRegistryPolicy" in body and ".transfer .alice .treasury" in body,
         "no-grant negative scenario does not test an ungranted destination")

def uncontrolled_recipient():
    src = load("SIRMTests.lean")
    need("theorem treasuryDoesNotControlAlice" in src,
         "missing proof that Treasury does not control Alice")
    need("theorem controlledTreasuryMayIssueToUncontrolledAlice" in src,
         "missing successful issue-to-uncontrolled-recipient scenario")
    need("DemoPrincipal.treasury DemoAccount.treasury DemoAccount.alice" in src and
         "(.issue .treasury .alice)" in src,
         "Treasury-to-Alice issue scope is not explicit")

def controlled_financial_trace():
    src = load("SIRMTests.lean")
    marker = "/-! ### Integration with the existing financial state machine -/"
    need(src.count(marker) == 1, "financial integration marker is missing or duplicated")
    integration = src.split(marker, 1)[1]
    need("demoControlledRegistryPolicy" in integration,
         "financial trace does not use the combined control+grant policy")
    need("demoRegistryPolicy" not in integration,
         "legacy grant-only policy remains in the financial integration trace")

def pinned_toolchain_and_test_driver():
    toolchain = load("lean-toolchain").strip()
    lake = load("lakefile.toml")
    need(toolchain == "leanprover/lean4:v4.33.1",
         f"unexpected Lean toolchain: {toolchain}")
    need('rev = "v4.33.1"' in lake,
         "Mathlib revision is not pinned to v4.33.1")
    need('testDriver = "SIRMTests"' in lake,
         "Lake test driver is not SIRMTests")

def docs_and_ci_topology():
    readme = load("README.md")
    testing = load("docs/TESTING.md")
    formal = load("docs/FORMALIZATION_STATUS.md")
    security = load("docs/SECURITY_MODEL.md")
    replay = load("SIRM/ReplayProtectedAssetMigration.lean")
    fees = load("SIRM/FeeAccounting.lean")
    escrow = load("SIRM/EscrowAccounting.lean")
    time_locks = load("SIRM/EscrowTimeLocks.lean")
    disputes = load("SIRM/EscrowDisputes.lean")
    envelope = load("SIRM/FinancialTransactionEnvelope.lean")
    denials = load("SIRM/FinancialTransactionDenials.lean")
    umbrella = load("SIRM.lean")
    regression = load("SIRMTests.lean")
    workflow = load(".github/workflows/lean.yml")

    need("SIRM.AccountControl" in readme and "SIRM.AuthorityRegistry" in readme,
         "README does not describe the account-control and authority modules")
    for theorem in (
        "registryGrantWithoutAccountControlIsDenied",
        "registryAccountControlWithoutGrantIsDenied",
        "controlledTreasuryMayIssueToUncontrolledAlice",
    ):
        need(theorem in testing, f"TESTING.md does not document {theorem}")
    need("many-to-many" in formal.lower() and "issuer" in formal.lower(),
         "FORMALIZATION_STATUS.md does not describe static account control and issuer scope")
    need("recipient" in security.lower() and "static" in security.lower(),
         "SECURITY_MODEL.md does not describe the static authorization boundary")
    need("SIRM.FeeAccounting" in umbrella and "SIRM.FeeAccounting" in readme,
         "fee accounting module is not integrated/documented")
    need("feeTransferStep_preserves_conservation" in fees and
         "FeeAuthorizationPolicy" in fees and "feeTransferJournal" in fees,
         "fee accounting lacks separate authorization, combined journal, or conservation theorem")
    for theorem in (
        "feeAccounting_gross_splits_into_net_and_fee",
        "feeAccounting_zero_fee_preserves_gross_amount",
        "feeAccounting_full_fee_leaves_zero_net",
        "feeAccounting_fee_above_gross_is_not_admissible",
    ):
        need(theorem in regression, f"SIRMTests.lean missing {theorem}")
    need("SIRM.ReplayProtectedAssetMigration" in umbrella and
         "SIRM.ReplayProtectedAssetMigration" in readme,
         "replay-protected migration module is not integrated/documented")
    need("nextNonce : Principal → Nat" in replay and
         "nonce = before.nextNonce principal" in replay and
         "nonce + 1" in replay,
         "replay guard does not require and advance the per-principal next nonce")
    for theorem in (
        "demoReplayProtected_stale_nonce_zero_rejected",
        "demoReplayProtected_future_nonce_two_rejected",
        "demoReplayProtected_other_principal_nonce_is_unchanged",
        "demoReplayProtected_preserves_complete_invariant",
    ):
        need(theorem in regression,
             f"SIRMTests.lean does not document/compile {theorem}")

    need("SIRM.EscrowAccounting" in umbrella and "SIRM.EscrowAccounting" in readme,
         "escrow accounting module is not integrated/documented")
    need("SIRM.EscrowTimeLocks" in umbrella and "SIRM.EscrowTimeLocks" in readme,
         "escrow time-lock module is not integrated/documented")
    need("SIRM.FinancialTransactionEnvelope" in umbrella and
         "SIRM.FinancialTransactionEnvelope" in readme,
         "typed financial transaction-envelope module is not integrated/documented")
    for declaration in (
        "FinancialTransactionEnvelopeSuccessStep",
        "FinancialTransactionEnvelopeReplayStep",
        "FinancialTransactionRequestIdConflict",
        "FinancialTransactionReceiptInvariant",
        "financialTransactionEnvelopeInvariant_of_reachable",
        "financialTransactionEnvelopeSuccess_rejects_same_nonce_competitor",
    ):
        need(declaration in envelope,
             f"FinancialTransactionEnvelope.lean is missing {declaration}")
    for theorem in (
        "demoFinancialEnvelope_transfer_success",
        "demoFinancialEnvelope_exact_retry_returns_cached_response",
        "demoFinancialEnvelope_conflicting_payload_rejected",
        "demoFinancialEnvelope_same_nonce_competitor_rejected",
        "demoFinancialEnvelope_old_nonce_new_id_rejected",
        "demoFinancialEnvelope_reachable_state_preserves_conservation",
    ):
        need(theorem in regression,
             f"SIRMTests.lean missing transaction-envelope regression {theorem}")
    need("## Typed financial transaction-envelope regressions" in testing,
         "TESTING.md does not document typed transaction-envelope regressions")
    need("SIRM.FinancialTransactionDenials" in umbrella and
         "SIRM.FinancialTransactionDenials" in readme,
         "authorization-denial cache module is not integrated/documented")
    for declaration in (
        "FinancialTransactionInsufficientFundsDenial",
        "FinancialTransactionInsufficientFundsDenialStep",
        "financialTransactionProcessorInsufficientFunds_preserves_invariant",
        "financialTransactionInsufficientFunds_rejects_nonce_mismatch",
    ):
        need(declaration in denials,
             f"FinancialTransactionDenials.lean is missing {declaration}")
    for theorem in (
        "demoFinancialProcessor_transfer_is_insufficient_funds",
        "demoFinancialProcessor_insufficient_funds_is_admitted_at_current_nonce",
        "demoFinancialProcessor_insufficient_funds_does_not_change_financial_state",
        "demoFinancialProcessor_insufficient_funds_does_not_consume_nonce",
        "demoFinancialProcessor_insufficient_funds_preserves_every_nonce",
        "demoFinancialProcessor_insufficient_funds_response_replays",
        "demoFinancialProcessor_burn_insufficient_funds_is_admitted_at_current_nonce",
        "demoFinancialProcessor_burn_insufficient_funds_response_replays",
        "demoFinancialProcessor_issue_is_not_insufficient_funds_denial",
        "demoFinancialProcessor_self_transfer_is_not_insufficient_funds_denial",
        "demoFinancialProcessor_unauthorized_transfer_is_not_insufficient_funds_denial",
        "demoFinancialProcessor_burn_is_insufficient_funds",
        "demoInsufficientFundsFinancialProcessor_reachable_invariant",
    ):
        need(theorem in regression,
             f"SIRMTests.lean missing insufficient-funds regression {theorem}")
    need("## Cached insufficient-funds regressions" in testing,
         "TESTING.md does not document cached insufficient-funds regressions")
    need("insufficient-funds denials" in readme,
         "README does not describe insufficient-funds denial semantics")

    for declaration in (
        "FinancialTransactionAuthorizationDenialStep",
        "FinancialTransactionProcessorSuccessStep",
        "FinancialTransactionProcessorReplayStep",
        "FinancialTransactionProcessorCacheDisjoint",
        "financialTransactionProcessorInvariant_of_reachable",
        "financialTransactionAuthorizationDenial_rejects_nonce_mismatch",
    ):
        need(declaration in denials,
             f"FinancialTransactionDenials.lean is missing {declaration}")
    for theorem in (
        "demoFinancialProcessor_denial_is_admitted_at_current_nonce",
        "demoFinancialProcessor_denial_does_not_consume_nonce",
        "demoFinancialProcessor_success_with_new_id_after_policy_change",
        "demoFinancialProcessor_denial_response_replays_after_nonce_advance",
        "demoFinancialProcessor_old_denial_remains_exact_replay",
        "demoDeniedFinancialProcessor_reachable_invariant",
    ):
        need(theorem in regression,
             f"SIRMTests.lean missing authorization-denial regression {theorem}")
    need("## Cached authorization-denial regressions" in testing,
         "TESTING.md does not document cached authorization-denial regressions")
    need("EscrowOpenStep" in escrow and "EscrowReleaseStep" in escrow and
         "EscrowCancelStep" in escrow and "escrowFinancialStep_preserves_invariant" in escrow,
         "escrow lifecycle is missing an operation or invariant-preservation theorem")
    for theorem in (
        "escrowDemo_open_exact_balances",
        "escrowDemo_release_exact_balances",
        "escrowDemo_cancel_exact_balances",
        "escrowDemo_open_denied_without_escrow_permission",
        "escrowDemo_open_cannot_repeat",
        "escrowDemo_release_cannot_repeat",
        "escrowDemo_cancel_cannot_repeat",
        "escrowDemo_open_after_release_is_denied",
        "escrowDemo_open_after_cancel_is_denied",
        "escrowDemo_cancel_after_release_is_denied",
        "escrowDemo_after_release_invariant",
        "escrowDemo_after_cancel_invariant",
    ):
        need(theorem in regression, f"SIRMTests.lean missing {theorem}")
    need("mayExpireEscrow" in escrow and "EscrowPhase.expired" in time_locks,
         "escrow timeout requires a dedicated permission and a distinct expired terminal phase")
    for declaration in (
        "EscrowTimeLockedFinancialRegistryState",
        "EscrowTimeLockedOpenStep",
        "EscrowTimeLockedReleaseStep",
        "EscrowTimeLockedCancelStep",
        "EscrowTimeLockedExpireStep",
        "EscrowTimeAdvanceStep",
        "escrowFinancialRegistryExpire_preserves_invariant",
        "escrowTimeLockedFinancialRegistryStep_preserves_invariant",
        "escrowTimeLockedFinancialRegistryStep_time_monotone",
        "escrowTimeLockedReleaseStep_rejects_expired",
        "escrowTimeLockedCancelStep_rejects_expired",
        "escrowTimeLockedExpireStep_requires_elapsed_deadline",
        "escrowRegistryExpire_other",
        "escrowTimeLockedFinancialRegistryInvariant_of_reachable",
    ):
        need(declaration in time_locks,
             f"EscrowTimeLocks.lean is missing {declaration}")
    for theorem in (
        "integratedEscrowTime_open_alpha_step",
        "integratedEscrowTime_open_beta_step",
        "integratedEscrowTime_advance_to_beta_deadline",
        "integratedEscrowTime_time_step_is_monotone",
        "integratedEscrowTime_expire_beta_step",
        "integratedEscrowTime_beta_open_blocked_at_deadline",
        "integratedEscrowTime_beta_release_blocked_at_deadline",
        "integratedEscrowTime_beta_cancel_blocked_at_deadline",
        "integratedEscrowTime_beta_expiry_is_not_available_early",
        "integratedEscrowTime_expiry_requires_dedicated_permission",
        "integratedEscrowTime_after_beta_expiry_invariant",
        "integratedEscrowTime_after_expiry_vault_balance_is_40",
        "integratedEscrowTime_after_expiry_gl_subledger_is_40",
        "integratedEscrowTime_after_expiry_pending_pool_is_40",
        "integratedEscrowTime_alpha_record_remains_pending",
        "integratedEscrowTime_beta_record_is_expired",
        "integratedEscrowTime_expired_id_cannot_be_reused",
    ):
        need(theorem in regression,
             f"SIRMTests.lean missing escrow time-lock regression {theorem}")
    need("## Escrow expiry and time-lock regressions" in testing,
         "TESTING.md does not document escrow expiry and time-lock regressions")
    need("SIRM.EscrowDisputes" in umbrella and "SIRM.EscrowDisputes" in readme,
         "escrow dispute-freeze module is not integrated/documented")
    for declaration in (
        "EscrowDisputeFinancialRegistryState",
        "EscrowDisputeAuthorizationPolicy",
        "EscrowDisputeRaiseStep",
        "EscrowDisputeTimeLockedReleaseStep",
        "EscrowDisputeTimeLockedCancelStep",
        "EscrowDisputeTimeLockedExpireStep",
        "EscrowDisputeFinancialRegistryStep",
        "escrowDisputeRaiseStep_rejects_existing_filing",
        "escrowDisputeFinancialRegistryStep_preserves_existing_filing",
        "escrowDisputeFinancialRegistryStep_preserves_invariant",
        "escrowDisputeTimeLockedReleaseStep_rejects_disputed",
        "escrowDisputeTimeLockedCancelStep_rejects_disputed",
        "escrowDisputeTimeLockedExpireStep_rejects_disputed",
        "escrowDisputeRaiseStep_rejects_elapsed_deadline",
        "escrowDisputeFinancialRegistryStep_time_monotone",
        "escrowDisputeFinancialRegistryInvariant_of_reachable",
    ):
        need(declaration in disputes,
             f"EscrowDisputes.lean is missing {declaration}")
    for theorem in (
        "integratedEscrowDispute_beta_claim_step",
        "integratedEscrowDispute_after_beta_claim_reachable",
        "integratedEscrowDispute_beta_release_is_frozen",
        "integratedEscrowDispute_beta_cancel_is_frozen",
        "integratedEscrowDispute_beta_claim_cannot_be_filed_twice",
        "integratedEscrowDispute_alpha_remains_releasable",
        "integratedEscrowDispute_beta_filing_persists_after_clock_advance",
        "integratedEscrowDispute_advance_to_beta_deadline",
        "integratedEscrowDispute_beta_expiry_is_frozen_at_deadline",
        "integratedEscrowDispute_new_claim_is_rejected_at_deadline",
        "integratedEscrowDispute_after_deadline_reachable",
        "integratedEscrowDispute_beta_vault_funds_remain_65",
        "integratedEscrowDispute_other_alpha_id_is_not_frozen",
        "integratedEscrowDispute_after_deadline_preserves_invariant",
    ):
        need(theorem in regression,
             f"SIRMTests.lean missing escrow dispute-freeze regression {theorem}")
    need("## Escrow dispute-freeze regressions" in testing,
         "TESTING.md does not document escrow dispute-freeze regressions")
    decisions = load("docs/DECISIONS.md")
    journal = load("docs/DEVELOPMENT_JOURNAL.md")
    workflow = load("docs/SESSION_WORKFLOW.md")
    scope = load("docs/MATHEMATICAL_SCOPE.md")
    need("Layered escrow accounting and dispute safety" in decisions,
         "DECISIONS.md does not record the layered escrow/dispute decision")
    need("Work block: first-stage escrow dispute intake/freeze" in journal,
         "DEVELOPMENT_JOURNAL.md lacks the verified dispute-intake handoff")
    need("5bb3fd4f4d58436debce6abfab4c87df132632c8" in workflow and "PR #24" in workflow,
         "SESSION_WORKFLOW.md lacks the merged PR #24 baseline")
    need("first-stage dispute intake/freeze" in scope.lower(),
         "MATHEMATICAL_SCOPE.md does not describe the first-stage dispute freeze")
    need("SIRM.EscrowDisputes" in security and "dispute fairness/adjudication" in security,
         "SECURITY_MODEL.md does not distinguish the formal freeze from open dispute fairness/adjudication")

    workflow = load(".github/workflows/lean.yml")
    ids = re.findall(r"(?m)^\s+- id:", workflow)
    need(len(ids) == 17, f"expected 17 static matrix jobs, found {len(ids)}")
    workflows = list((ROOT / ".github/workflows").glob("*.yml"))
    workflows += list((ROOT / ".github/workflows").glob("*.yaml"))
    need(len(workflows) == 1, f"expected one workflow file, found {len(workflows)}")
    need("build: true" in workflow and "test: true" in workflow and "lint: false" in workflow,
         "Lean workflow must build, test, and explicitly keep lint disabled")
    need("cargo test --locked" in workflow and "cargo clippy --all-targets --locked -- -D warnings" in workflow
         and "cargo fmt --check" in workflow,
         "Lean workflow must run the Rust crate fmt, clippy and tests")

    broken = []
    for match in re.finditer(r"!?\[[^\]]*\]\(([^)]+)\)", readme):
        target = match.group(1).strip().split()[0].strip("<>")
        parsed = urlsplit(target)
        if parsed.scheme or target.startswith("//") or not parsed.path:
            continue
        local = ROOT / unquote(parsed.path)
        if not local.exists():
            broken.append(target)
    need(not broken, "broken local README links: " + ", ".join(broken))

CHECKS = {
    "no-proof-holes": no_proof_holes,
    "issue-api-shape": issue_api_shape,
    "issuer-recipient-scope": issuer_recipient_scope,
    "registry-issue-adapter": registry_issue_adapter,
    "finite-control-relation": finite_control_relation,
    "transfer-dual-gate": transfer_dual_gate,
    "issue-dual-gate": issue_dual_gate,
    "burn-dual-gate": burn_dual_gate,
    "issue-credits-recipient": issue_credits_recipient,
    "holder-machine-issuer": holder_machine_issuer,
    "financial-machine-issuer": financial_machine_issuer,
    "deny-grant-without-control": deny_grant_without_control,
    "deny-control-without-grant": deny_control_without_grant,
    "uncontrolled-recipient": uncontrolled_recipient,
    "controlled-financial-trace": controlled_financial_trace,
    "pinned-toolchain-and-test-driver": pinned_toolchain_and_test_driver,
    "docs-and-ci-topology": docs_and_ci_topology,
}

def main():
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 scripts/ci_audit.py <check-id|all>")
    selected = list(CHECKS) if sys.argv[1] == "all" else [sys.argv[1]]
    for name in selected:
        if name not in CHECKS:
            raise SystemExit(f"Unknown check: {name}")
        CHECKS[name]()
        print(f"PASS: {name}")
    print(f"STATIC_AUDITS_PASSED={len(selected)}")

if __name__ == "__main__":
    main()
