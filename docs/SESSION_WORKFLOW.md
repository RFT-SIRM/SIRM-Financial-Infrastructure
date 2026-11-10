# Session Workflow and Formalization Handoff

This file is the required starting protocol for every new implementation session. Read it together with the current `main` SHA, `docs/ROADMAP.md`, `docs/FORMALIZATION_STATUS.md`, the latest development-journal entries, and the actual source/tests. Do not rely on an old chat transcript as the source of repository state.

## 1. Establish facts before proposing edits

1. Fetch the repository and record the exact `main` SHA.
2. Read the latest roadmap, formalization status, architecture decisions, mathematical scope, testing instructions, and recent journal entries.
3. Inspect the target module, its direct dependencies, the umbrella import, theorem regression tests, and the relevant CI audit implementation.
4. Inspect recent commits/PRs and any failed CI logs relevant to the target. Reuse proven patterns from the current source; do not reconstruct them from memory.
5. Create one task branch directly from the verified `main` SHA. Confirm branch base and clean working tree before editing.
6. State the narrow objective, exact invariants, assumptions, non-goals, expected files, and verification commands before applying the patch.

Never start coding from a guessed continuation point. Repository state and source are authoritative.

## 2. Lean debugging: diagnose the actual goal, not the remembered error

1. Reproduce the first current compiler error on the exact worktree. Capture the complete message, source location, expected type, actual type, and unsolved goal.
2. Read the declaration and all relevant definitions/instances at that location. Check implicit versus explicit parameters, binder order, reducibility, coercions, namespaces, and typeclass assumptions.
3. Compare with an existing compiling theorem that has the same shape. Prefer a small local proof change grounded in that comparison.
4. Fix one root cause at a time. Re-run the narrow target build immediately; do not stack speculative edits.
5. After the target module compiles, run the full library build, then `lake test`. A library build does not substitute for the test driver.
6. If a regression fails, inspect the exact residual goal. Do not repeatedly add broad `simp` lists, `norm_num`, `omega`, `subst`, or unfolding names without checking whether they address the displayed goal. In particular, inspect reducibility and constructor shape before trying substitution; inspect membership constructors and empty/singleton cases before substituting list-membership variables; unfold state constructors when a test leaves projections of an empty state opaque.
7. Do not change theorem statements, weaken hypotheses, add axioms, or introduce `sorry`/`admit` merely to make compilation pass. Any genuine specification change must be justified and documented.
8. When a command fails, stop the pipeline and diagnose that failure. Do not claim later checks passed.

## 3. Patch and script discipline

- Prefer a small, reviewable patch to a sequence of versioned repair scripts.
- Before writing a patch script, inspect the exact current source and assert its expected old text occurs exactly once. If the anchor differs, stop without writing anything.
- Make patch application atomic: prepare complete new contents, validate all expected anchors and file paths, then write. Never leave a partially applied multi-file patch.
- Do not make the user manually edit Lean source or splice fragments. Provide one complete, tested command/script for the user's environment when local execution is required.
- Verify every generated/downloadable file exists at the exact path before linking it. Never infer a sandbox path from a filename.
- Avoid duplicate CI: do not push while another intended run is active; do not create extra branches or parallel PRs for the same task.

## 4. Mandatory verification and delivery gate

Run from the repository root, in this order:

```bash
lake build <Target.Module>
lake build SIRM
lake test
python3 scripts/ci_audit.py all
git diff --check
```

Then:
1. Inspect `git status --short`, `git diff --stat`, `git diff --name-status`, and the complete diff.
2. Stage only the reviewed task files; require no unstaged residue and run `git diff --cached --check`.
3. Inspect the complete staged diff. Verify no proof placeholders or accidental unrelated changes.
4. Only after every local check succeeds, create exactly one commit and one non-force push.
5. Verify the remote branch SHA equals the commit SHA and compare it to the exact intended base.
6. Open one PR to `main`. Confirm the PR head SHA and inspect all 18 checks (one Lean job plus 17 static audits).
7. Never merge on an assumption or a partial green result. Merge only when every required check for the exact PR head SHA has completed successfully. Prefer squash merge.
8. Verify the PR is merged and that `main` points to the returned merge SHA.

A test result is valid only for the exact source tree and commit on which it ran. Record command outputs, check counts, branch, base, commit, PR, and merge SHA in the journal.

## 5. Continuity between sessions

At the end of every block, update the development journal with:
- exact starting base and final commit/merge SHA;
- intended design and explicit non-goals;
- changed files and public declarations;
- exact verification commands and actual results;
- failed attempts that revealed a real constraint, with the corrected approach;
- remaining obligations and the next narrowly scoped task.

The next session must read the newest journal entry and verify its SHAs against GitHub before continuing. Do not repeat a failed approach unless new source evidence explains why it should now work.

## 6. Current workflow baseline

As of the authorized atomic migration block:
- PR #10 is squash-merged.
- Merge commit on `main`: `f6740483006d45bfc82b04fd441f49aac1865e52`.
- The PR head was `0ce1b999f893a5696e6ebee3ffb66465898f28a9`.
- GitHub Actions run #45 completed successfully: Lean plus all 17 static checks (18/18).
- The migration is an abstract atomic transition with exact route/source/recipient-scoped residual carry-forward. It does not implement external bridge settlement/finality, replay/idempotency, custody, rollback, or production backing/valuation of residual claims.

Update this baseline in the next journal entry; do not treat it as permanent state.


## 7. Current replay-guard work block

The next implementation branch is `foundation/transaction-replay-guard-2026-11-10`, based on the verified `main` SHA `f6740483006d45bfc82b04fd441f49aac1865e52`. Its goal is a migration-specific, per-principal sequential nonce gate layered over `SIRM.AuthorizedAssetMigration`. The exact accepted nonce must equal the principal's expected nonce; the migration and increment are one abstract state transition. The module, Lean tests, CI audit assertions, roadmap, formalization status, scope, testing guide, decisions, and journal must move together.

This block does not claim global transaction replay protection, request-hash idempotency, signature/expiry handling, persistence, concurrency semantics, or production nonce-width safety. Verify the latest branch and CI state before continuing; do not assume this paragraph means the block is merged.


## 8. Completed replay guard and documentation consolidation

- PR #11 feature head: `4e95e912898e310d927afcae0de507181eb7dd65`.
- PR #11 exact base: `f6740483006d45bfc82b04fd441f49aac1865e52`.
- PR #11 passed all 18 checks (one Lean job plus 17 static audits); squash merge on `main`: `8588b61401b6eae02510fc5f9772acf47e0dd3e5`.
- Replay protection is migration-scoped: exact expected nonce per principal, accepted principal advances in the same abstract transition, and other principals remain unchanged. It is not global idempotency or runtime persistence.
- Documentation consolidation branch: `docs/public-roadmap-status-2026-11-10`, based on that exact merge SHA. Its purpose is the illustrated README overview, author statement, and aligned roadmap/formalization boundaries.
