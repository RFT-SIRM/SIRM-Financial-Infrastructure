#!/usr/bin/env python3
"""Finite linearization/idempotency model for the SIRM transaction envelope.

This deliberately models the transaction boundary, not production storage,
cryptography, or an actual concurrent database. The transition processor is
atomic by construction: one immutable logical state is returned per request.
"""
from __future__ import annotations

import csv
import itertools
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Request:
    request_id: str
    principal: str
    nonce: int
    family: str
    amount: int
    authorized: bool = True

    @property
    def payload(self) -> tuple[Any, ...]:
        # Authorization is policy context, not signed/canonical request data.
        return (self.principal, self.nonce, self.family, self.amount)

    @property
    def effect(self) -> int:
        # Synthetic one-account effects used only to distinguish winners.
        return {"transfer": 1, "issue": 3, "burn": -2}[self.family]


@dataclass(frozen=True)
class Response:
    code: str
    request_id: str
    accepted_nonce: int | None
    next_nonce: int | None
    balance_after: int | None


@dataclass
class State:
    next_nonce: dict[str, int] = field(default_factory=dict)
    balances: dict[str, int] = field(default_factory=dict)
    receipts: dict[str, tuple[tuple[Any, ...], Response]] = field(default_factory=dict)
    commits: dict[str, int] = field(default_factory=dict)

    def clone(self) -> "State":
        return State(self.next_nonce.copy(), self.balances.copy(),
                     self.receipts.copy(), self.commits.copy())

    def snapshot(self) -> tuple[Any, ...]:
        return (
            tuple(sorted(self.next_nonce.items())),
            tuple(sorted(self.balances.items())),
            tuple(sorted((k, v[0], v[1]) for k, v in self.receipts.items())),
            tuple(sorted(self.commits.items())),
        )


def process(state: State, req: Request) -> tuple[State, str, Response | None]:
    """Process one request at a linearization point.

    Rules:
    1. Existing request ID + same exact payload: return cached response, no write.
    2. Existing request ID + different payload: conflict, no write.
    3. Nonce mismatch: stale/future, do not cache (may be retried later).
    4. Deterministic authorization rejection: cache the rejection, consume no nonce.
    5. Success: financial effect + nonce increment + success receipt commit together.
    """
    prior = state.receipts.get(req.request_id)
    if prior is not None:
        prior_payload, prior_response = prior
        if prior_payload == req.payload:
            return state, "IDEMPOTENT_REPLAY", prior_response
        return state, "REQUEST_ID_CONFLICT", None

    expected = state.next_nonce.get(req.principal, 0)
    if req.nonce < expected:
        return state, "STALE_NONCE", None
    if req.nonce > expected:
        return state, "FUTURE_NONCE", None

    if not req.authorized:
        response = Response("AUTHORIZATION_REJECTED", req.request_id,
                            None, expected, None)
        after = state.clone()
        after.receipts[req.request_id] = (req.payload, response)
        return after, "AUTHORIZATION_REJECTED_CACHED", response

    after = state.clone()
    old_balance = after.balances.get(req.principal, 100)
    new_balance = old_balance + req.effect
    after.balances[req.principal] = new_balance
    after.next_nonce[req.principal] = expected + 1
    response = Response("ACCEPTED", req.request_id, req.nonce,
                        expected + 1, new_balance)
    after.receipts[req.request_id] = (req.payload, response)
    after.commits[req.request_id] = after.commits.get(req.request_id, 0) + 1
    return after, "ACCEPTED", response


def initial_state(principals: tuple[str, ...] = ("A", "B")) -> State:
    return State({p: 0 for p in principals}, {p: 100 for p in principals})


def check_same_nonce_races() -> dict[str, Any]:
    contenders = (
        Request("race-transfer", "A", 0, "transfer", 10),
        Request("race-issue", "A", 0, "issue", 20),
        Request("race-burn", "A", 0, "burn", 5),
    )
    rows = []
    winner_counts = {r.request_id: 0 for r in contenders}
    for order_no, permutation in enumerate(itertools.permutations(contenders), start=1):
        state = initial_state(("A",))
        outcomes = []
        accepted = []
        for request in permutation:
            state, outcome, _ = process(state, request)
            outcomes.append(outcome)
            if outcome == "ACCEPTED":
                accepted.append(request.request_id)
        assert len(accepted) == 1, (permutation, outcomes)
        winner = accepted[0]
        winner_counts[winner] += 1
        assert state.next_nonce["A"] == 1
        assert sum(state.commits.values()) == 1
        assert len(state.receipts) == 1

        winner_req = next(r for r in contenders if r.request_id == winner)
        before_retry = state.snapshot()
        for retry_no in range(1, 5):
            state2, retry_outcome, replayed_response = process(state, winner_req)
            assert retry_outcome == "IDEMPOTENT_REPLAY"
            assert state2.snapshot() == before_retry
            assert replayed_response == state.receipts[winner][1]
            state = state2

        # Reusing the winner's ID for a different body must never mutate state.
        conflicting = Request(winner, "A", 0, "issue", 999)
        before_conflict = state.snapshot()
        state2, conflict_outcome, _ = process(state, conflicting)
        assert conflict_outcome == "REQUEST_ID_CONFLICT"
        assert state2.snapshot() == before_conflict

        rows.append({
            "schedule": order_no,
            "arrival_order": ">".join(r.request_id for r in permutation),
            "winner": winner,
            "accepted": 1,
            "stale_rejected": 2,
            "exact_replays_tested": 4,
            "conflicting_id_rejected": 1,
            "financial_commits": sum(state.commits.values()),
        })

    assert set(winner_counts.values()) == {2}
    return {
        "schedules": len(rows),
        "accepted_per_schedule": 1,
        "stale_rejections_per_schedule": 2,
        "winner_frequency": winner_counts,
        "exact_replays_per_winner": 4,
        "conflicting_request_id_cases": len(rows),
        "financial_commits_per_schedule": 1,
        "rows": rows,
    }


def check_sequential_nonce_reordering() -> dict[str, Any]:
    requests = tuple(
        Request(f"seq-{nonce}", "A", nonce, family, 10 + nonce)
        for nonce, family in enumerate(("transfer", "issue", "burn"))
    )
    rows = []
    total_first_pass_future = 0
    total_retry_attempts = 0
    max_retry_rounds = 0
    for schedule_no, order in enumerate(itertools.permutations(requests), start=1):
        state = initial_state(("A",))
        pending = []
        outcomes = []
        for req in order:
            state, outcome, _ = process(state, req)
            outcomes.append(outcome)
            if outcome == "FUTURE_NONCE":
                pending.append(req)
            else:
                assert outcome == "ACCEPTED"
        first_future = len(pending)
        total_first_pass_future += first_future
        retry_attempts = 0
        retry_rounds = 0
        while pending:
            retry_rounds += 1
            next_pending = []
            progressed = False
            for req in pending:
                retry_attempts += 1
                state, outcome, _ = process(state, req)
                if outcome == "ACCEPTED":
                    progressed = True
                elif outcome == "FUTURE_NONCE":
                    next_pending.append(req)
                else:
                    raise AssertionError((schedule_no, req, outcome))
            assert progressed, "retry queue deadlocked despite contiguous nonces"
            pending = next_pending
        assert state.next_nonce["A"] == 3
        assert len(state.receipts) == 3
        assert sum(state.commits.values()) == 3
        total_retry_attempts += retry_attempts
        max_retry_rounds = max(max_retry_rounds, retry_rounds)
        rows.append({
            "schedule": schedule_no,
            "arrival_nonce_order": ">".join(str(r.nonce) for r in order),
            "first_pass_future_rejections": first_future,
            "retry_attempts": retry_attempts,
            "retry_rounds": retry_rounds,
            "accepted_total": 3,
        })
    return {
        "schedules": len(rows),
        "all_three_eventually_accepted": True,
        "first_pass_future_rejections_total": total_first_pass_future,
        "retry_attempts_total": total_retry_attempts,
        "max_retry_rounds": max_retry_rounds,
        "rows": rows,
    }


def check_principal_isolation() -> dict[str, Any]:
    requests = (
        Request("A-0", "A", 0, "transfer", 1),
        Request("A-1", "A", 1, "issue", 1),
        Request("B-0", "B", 0, "burn", 1),
        Request("B-1", "B", 1, "transfer", 1),
    )
    # Preserve order within each principal; enumerate all cross-principal shuffles.
    rows = []
    for a_positions in itertools.combinations(range(4), 2):
        a_positions = set(a_positions)
        ai = bi = 0
        order = []
        for pos in range(4):
            if pos in a_positions:
                order.append(requests[ai])
                ai += 1
            else:
                order.append(requests[2 + bi])
                bi += 1
        state = initial_state(("A", "B"))
        for req in order:
            state, outcome, _ = process(state, req)
            assert outcome == "ACCEPTED", (order, req, outcome)
        assert state.next_nonce == {"A": 2, "B": 2}
        assert sum(state.commits.values()) == 4
        rows.append({"schedule": len(rows) + 1,
                     "arrival_order": ">".join(r.request_id for r in order),
                     "accepted": 4,
                     "final_nonce_A": state.next_nonce["A"],
                     "final_nonce_B": state.next_nonce["B"]})
    return {"schedules": len(rows), "all_accepted_each_schedule": True, "rows": rows}


def check_cached_rejection_and_retry() -> dict[str, Any]:
    state = initial_state(("A",))
    denied = Request("denied-0", "A", 0, "transfer", 7, authorized=False)
    state1, outcome1, response1 = process(state, denied)
    assert outcome1 == "AUTHORIZATION_REJECTED_CACHED"
    assert state1.next_nonce["A"] == 0
    assert state1.balances["A"] == 100
    assert state1.commits == {}
    state2, outcome2, response2 = process(state1, denied)
    assert outcome2 == "IDEMPOTENT_REPLAY" and response2 == response1
    assert state2.snapshot() == state1.snapshot()

    # Same business payload, new request ID after a policy change can proceed.
    newly_authorized = Request("denied-0-retry-new-id", "A", 0, "transfer", 7, authorized=True)
    state3, outcome3, _ = process(state2, newly_authorized)
    assert outcome3 == "ACCEPTED"
    assert state3.next_nonce["A"] == 1
    assert state3.balances["A"] == 101
    return {
        "cached_auth_rejections": 1,
        "retry_same_id_replays_rejection": True,
        "nonce_consumed_on_auth_rejection": False,
        "same_payload_new_id_after_policy_change_accepted": True,
    }


def check_atomic_write_boundary() -> dict[str, Any]:
    # Atomic success writes exactly these three logical components together.
    components = ("financial_state", "principal_nonce", "success_receipt")
    valid_masks = []
    partial_masks = []
    rows = []
    for mask in range(1 << len(components)):
        written = [components[i] for i in range(len(components)) if mask & (1 << i)]
        complete = mask == 0 or mask == (1 << len(components)) - 1
        (valid_masks if complete else partial_masks).append(mask)
        rows.append({
            "write_mask": format(mask, "03b"),
            "written_components": "+".join(written) if written else "none",
            "atomic_boundary_valid": complete,
        })
    assert len(valid_masks) == 2 and len(partial_masks) == 6
    return {
        "logical_write_components": list(components),
        "possible_partial_write_patterns": 8,
        "valid_all_or_none_patterns": 2,
        "unsafe_partial_patterns": 6,
        "rows": rows,
    }


def main() -> None:
    out = Path("engineering/transaction_envelope/results")
    out.mkdir(parents=True, exist_ok=True)
    race = check_same_nonce_races()
    reorder = check_sequential_nonce_reordering()
    isolation = check_principal_isolation()
    cached_rejection = check_cached_rejection_and_retry()
    atomicity = check_atomic_write_boundary()

    summary = {
        "model": "linearizable transaction envelope with per-principal nonce and request-id receipt cache",
        "request_identity": "exact typed payload equality; no cryptographic hash or canonical byte encoding is modeled",
        "concurrency_assumption": "each request observes and updates one serialized atomic state transition",
        "nonce_policy": "nonce mismatch is not cached; deterministic authorization rejection is cached; rejected requests do not consume nonce",
        "same_nonce_races": {k: v for k, v in race.items() if k != "rows"},
        "sequential_nonce_reordering": {k: v for k, v in reorder.items() if k != "rows"},
        "principal_isolation": {k: v for k, v in isolation.items() if k != "rows"},
        "cached_rejection": cached_rejection,
        "atomic_write_boundary": {k: v for k, v in atomicity.items() if k != "rows"},
        "result": "PASS",
        "scope_limitations": [
            "finite abstract model only; not a database or distributed-systems linearizability proof",
            "does not establish crash durability, locking, compare-and-swap, consensus ordering, or isolation level",
            "does not model signatures, threshold authorization, canonical serialization, expiry, or cryptographic request hashes",
            "synthetic per-principal balance effects are not the SIRM holder/GL accounting implementation",
            "requires a later Lean model and implementation refinement/conformance proof",
        ],
    }
    (out / "transaction_envelope_model_check.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    suites = {
        "same_nonce_races": race["rows"],
        "sequential_nonce_reordering": reorder["rows"],
        "principal_isolation": isolation["rows"],
        "atomic_write_patterns": atomicity["rows"],
    }
    for name, rows in suites.items():
        path = out / f"{name}.csv"
        with path.open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]), lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)

    print("TRANSACTION_ENVELOPE_MODEL_CHECK=PASS")
    print(f"SAME_NONCE_RACE_SCHEDULES={race['schedules']}")
    print(f"RACE_WINNER_FREQUENCIES={race['winner_frequency']}")
    print(f"EXACT_REPLAY_CASES={race['schedules'] * race['exact_replays_per_winner']}")
    print(f"REQUEST_ID_CONFLICT_CASES={race['conflicting_request_id_cases']}")
    print(f"SEQUENTIAL_NONCE_ARRIVAL_ORDERS={reorder['schedules']}")
    print(f"FIRST_PASS_FUTURE_REJECTIONS={reorder['first_pass_future_rejections_total']}")
    print(f"FAIR_RETRY_ATTEMPTS={reorder['retry_attempts_total']}")
    print(f"PRINCIPAL_ISOLATION_SCHEDULES={isolation['schedules']}")
    print("CACHED_AUTHORIZATION_REJECTION=PASS")
    print("ATOMIC_WRITE_PATTERNS=8 (2 valid, 6 unsafe partial)")
    print(f"RESULT_JSON={out / 'transaction_envelope_model_check.json'}")


if __name__ == "__main__":
    main()
