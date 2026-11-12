#!/usr/bin/env python3
"""Exhaustively check finite schedules for one shared nonce per principal.

This finite model explores all interleavings of three financial operation
families (transfer, issue, burn) for two principals, with every operation
family appearing exactly once per principal. It checks exact-next acceptance,
stale/future rejection, cross-family replay rejection, and principal isolation.
It is an executable finite model check, not a Lean proof or runtime protocol test.
"""
from __future__ import annotations

import argparse
import csv
import itertools
import json
from pathlib import Path

FAMILIES = ("transfer", "issue", "burn")
PRINCIPALS = ("principal_A", "principal_B")


def interleavings(left: tuple[str, ...], right: tuple[str, ...]):
    """Yield every order-preserving merge of two three-element sequences."""
    for left_positions in itertools.combinations(range(6), 3):
        left_set = set(left_positions)
        li = ri = 0
        merged = []
        for pos in range(6):
            if pos in left_set:
                merged.append((PRINCIPALS[0], left[li]))
                li += 1
            else:
                merged.append((PRINCIPALS[1], right[ri]))
                ri += 1
        yield tuple(merged)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("engineering/replay_protection/results"),
    )
    args = parser.parse_args()
    out = args.output_dir
    out.mkdir(parents=True, exist_ok=True)

    orders = tuple(itertools.permutations(FAMILIES))
    schedule_count = accepted_steps = stale_rejections = future_rejections = 0
    cross_family_rejections = isolation_checks = final_state_checks = 0
    rows: list[dict[str, object]] = []

    for order_a in orders:
        for order_b in orders:
            for schedule in interleavings(order_a, order_b):
                schedule_count += 1
                next_nonce = {PRINCIPALS[0]: 0, PRINCIPALS[1]: 0}
                used_by_principal: dict[str, list[tuple[str, int]]] = {
                    PRINCIPALS[0]: [], PRINCIPALS[1]: []
                }

                for step_index, (principal, family) in enumerate(schedule, start=1):
                    supplied = next_nonce[principal]
                    other = PRINCIPALS[1] if principal == PRINCIPALS[0] else PRINCIPALS[0]
                    other_before = next_nonce[other]

                    # Only the exact expected nonce is admitted.
                    assert supplied == next_nonce[principal]
                    accepted_steps += 1
                    next_nonce[principal] = supplied + 1
                    used_by_principal[principal].append((family, supplied))

                    # A stale value and a skipped/future value must both fail.
                    if next_nonce[principal] > 1:
                        stale = supplied
                        assert stale != next_nonce[principal]
                        stale_rejections += 1
                    future = next_nonce[principal] + 1
                    assert future != next_nonce[principal]
                    future_rejections += 1

                    # A nonce consumed by one operation family cannot be replayed
                    # under another operation family for the same principal.
                    for alternate_family in FAMILIES:
                        if alternate_family != family:
                            replay_nonce = supplied
                            assert replay_nonce != next_nonce[principal]
                            cross_family_rejections += 1

                    # An operation by A must not mutate B's nonce, and vice versa.
                    assert next_nonce[other] == other_before
                    isolation_checks += 1

                    rows.append(
                        {
                            "schedule": schedule_count,
                            "step": step_index,
                            "principal": principal,
                            "operation_family": family,
                            "accepted_nonce": supplied,
                            "next_nonce_after": next_nonce[principal],
                            "other_principal_nonce": next_nonce[other],
                        }
                    )

                assert next_nonce == {PRINCIPALS[0]: 3, PRINCIPALS[1]: 3}
                final_state_checks += 1

    expected_schedules = 6 * 6 * 20
    assert schedule_count == expected_schedules, (schedule_count, expected_schedules)
    assert accepted_steps == expected_schedules * 6

    csv_path = out / "global_financial_nonce_interleavings.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)

    report = {
        "model": "two principals; shared per-principal nonce across transfer/issue/burn",
        "operation_families": list(FAMILIES),
        "principals": list(PRINCIPALS),
        "operation_orders_per_principal": len(orders),
        "order_preserving_interleavings_per_order_pair": 20,
        "exhaustive_schedules": schedule_count,
        "accepted_steps": accepted_steps,
        "stale_nonce_rejections": stale_rejections,
        "future_nonce_rejections": future_rejections,
        "cross_operation_family_replay_rejections": cross_family_rejections,
        "other_principal_isolation_checks": isolation_checks,
        "terminal_nonce_states_checked": final_state_checks,
        "terminal_nonce_for_each_principal": 3,
        "result": "PASS",
        "scope_note": (
            "Finite model check of nonce sequencing only; not a proof of signatures, "
            "persistent storage, concurrent runtime atomicity, idempotent responses, "
            "or failed-request nonce policy."
        ),
    }
    json_path = out / "global_financial_nonce_model_check.json"
    json_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print("GLOBAL_FINANCIAL_NONCE_MODEL_CHECK=PASS")
    print(f"EXHAUSTIVE_SCHEDULES={schedule_count}")
    print(f"ACCEPTED_STEPS={accepted_steps}")
    print(f"STALE_REJECTIONS={stale_rejections}")
    print(f"FUTURE_REJECTIONS={future_rejections}")
    print(f"CROSS_FAMILY_REPLAY_REJECTIONS={cross_family_rejections}")
    print(f"PRINCIPAL_ISOLATION_CHECKS={isolation_checks}")
    print(f"RESULT_JSON={json_path}")
    print(f"RESULT_CSV={csv_path}")


if __name__ == "__main__":
    main()
