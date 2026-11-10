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

    ids = re.findall(r"(?m)^\s+- id:", workflow)
    need(len(ids) == 17, f"expected 17 static matrix jobs, found {len(ids)}")
    workflows = list((ROOT / ".github/workflows").glob("*.yml"))
    workflows += list((ROOT / ".github/workflows").glob("*.yaml"))
    need(len(workflows) == 1, f"expected one workflow file, found {len(workflows)}")
    need("build: true" in workflow and "test: true" in workflow and "lint: false" in workflow,
         "Lean workflow must build, test, and explicitly keep lint disabled")

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
