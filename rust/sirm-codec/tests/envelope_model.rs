//! Differential test: replays the finite scenarios of the Python model
//! (`scripts/model_check_transaction_envelope.py`) against the Rust port and
//! compares the aggregate counts with the committed model-check JSON.

use serde_json::Value;
use sirm_codec::envelope::*;

fn req(id: &str, principal: &str, nonce: u64, family: Family, amount: u64) -> Request {
    Request {
        request_id: id.into(),
        principal: principal.into(),
        nonce,
        family,
        amount,
        authorized: true,
    }
}

fn permutations<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(i);
        for mut p in permutations(&rest) {
            p.insert(0, head.clone());
            out.push(p);
        }
    }
    out
}

fn model() -> Value {
    serde_json::from_str(include_str!(
        "../../../engineering/transaction_envelope/results/transaction_envelope_model_check.json"
    ))
    .unwrap()
}

#[test]
fn same_nonce_races() {
    let contenders = vec![
        req("race-transfer", "A", 0, Family::Transfer, 10),
        req("race-issue", "A", 0, Family::Issue, 20),
        req("race-burn", "A", 0, Family::Burn, 5),
    ];
    let mut winners = std::collections::BTreeMap::<String, u32>::new();
    let orders = permutations(&contenders);
    for order in &orders {
        let mut s = State::with_principals(&["A"]);
        let mut accepted = vec![];
        let mut stale = 0;
        for r in order {
            match s.process(r).0 {
                Outcome::Accepted => accepted.push(r.clone()),
                Outcome::StaleNonce => stale += 1,
                o => panic!("unexpected {o:?}"),
            }
        }
        assert_eq!((accepted.len(), stale), (1, 2));
        let w = &accepted[0];
        *winners.entry(w.request_id.clone()).or_default() += 1;
        assert_eq!(s.next_nonce["A"], 1);
        assert_eq!(s.commit_total(), 1);
        assert_eq!(s.receipts.len(), 1);
        let stored = s.receipts[&w.request_id].1.clone();
        for _ in 0..4 {
            let before = s.clone();
            let (o, resp) = s.process(w);
            assert_eq!(o, Outcome::IdempotentReplay);
            assert_eq!(resp, Some(stored.clone()));
            assert_eq!(s, before);
        }
        let mut conflicting = w.clone();
        conflicting.family = Family::Issue;
        conflicting.amount = 999;
        let before = s.clone();
        assert_eq!(s.process(&conflicting).0, Outcome::RequestIdConflict);
        assert_eq!(s, before);
    }
    let m = &model()["same_nonce_races"];
    assert_eq!(orders.len() as u64, m["schedules"].as_u64().unwrap());
    for (id, n) in &winners {
        assert_eq!(
            *n as u64,
            m["winner_frequency"][id].as_u64().unwrap(),
            "{id}"
        );
    }
}

#[test]
fn sequential_nonce_reordering() {
    let families = [Family::Transfer, Family::Issue, Family::Burn];
    let reqs: Vec<Request> = families
        .iter()
        .enumerate()
        .map(|(n, f)| req(&format!("seq-{n}"), "A", n as u64, *f, 10 + n as u64))
        .collect();
    let (mut future_total, mut retry_total, mut max_rounds, mut schedules) =
        (0u64, 0u64, 0u64, 0u64);
    for order in permutations(&reqs) {
        schedules += 1;
        let mut s = State::with_principals(&["A"]);
        let mut pending = vec![];
        for r in &order {
            match s.process(r).0 {
                Outcome::Accepted => {}
                Outcome::FutureNonce => pending.push(r.clone()),
                o => panic!("unexpected {o:?}"),
            }
        }
        future_total += pending.len() as u64;
        let mut rounds = 0;
        while !pending.is_empty() {
            rounds += 1;
            let mut next = vec![];
            let mut progressed = false;
            for r in pending {
                retry_total += 1;
                match s.process(&r).0 {
                    Outcome::Accepted => progressed = true,
                    Outcome::FutureNonce => next.push(r),
                    o => panic!("unexpected {o:?}"),
                }
            }
            assert!(progressed, "retry queue deadlocked");
            pending = next;
        }
        max_rounds = max_rounds.max(rounds);
        assert_eq!(s.next_nonce["A"], 3);
        assert_eq!((s.receipts.len(), s.commit_total()), (3, 3));
    }
    let m = &model()["sequential_nonce_reordering"];
    assert_eq!(schedules, m["schedules"].as_u64().unwrap());
    assert_eq!(
        future_total,
        m["first_pass_future_rejections_total"].as_u64().unwrap()
    );
    assert_eq!(retry_total, m["retry_attempts_total"].as_u64().unwrap());
    assert_eq!(max_rounds, m["max_retry_rounds"].as_u64().unwrap());
}

#[test]
fn principal_isolation() {
    let a = [
        req("A-0", "A", 0, Family::Transfer, 1),
        req("A-1", "A", 1, Family::Issue, 1),
    ];
    let b = [
        req("B-0", "B", 0, Family::Burn, 1),
        req("B-1", "B", 1, Family::Transfer, 1),
    ];
    let mut schedules = 0u64;
    for i in 0..4 {
        for j in (i + 1)..4 {
            schedules += 1;
            let (mut ai, mut bi) = (0, 0);
            let mut s = State::with_principals(&["A", "B"]);
            for pos in 0..4 {
                let r = if pos == i || pos == j {
                    ai += 1;
                    &a[ai - 1]
                } else {
                    bi += 1;
                    &b[bi - 1]
                };
                assert_eq!(s.process(r).0, Outcome::Accepted);
            }
            assert_eq!((s.next_nonce["A"], s.next_nonce["B"]), (2, 2));
            assert_eq!(s.commit_total(), 4);
        }
    }
    assert_eq!(
        schedules,
        model()["principal_isolation"]["schedules"]
            .as_u64()
            .unwrap()
    );
}

#[test]
fn cached_rejection_and_retry() {
    let mut s = State::with_principals(&["A"]);
    let mut denied = req("denied-0", "A", 0, Family::Transfer, 7);
    denied.authorized = false;
    let (o1, r1) = s.process(&denied);
    assert_eq!(o1, Outcome::AuthorizationRejectedCached);
    assert_eq!((s.next_nonce["A"], s.balances["A"]), (0, 100));
    assert!(s.commits.is_empty());
    let snap = s.clone();
    let (o2, r2) = s.process(&denied);
    assert_eq!((o2, r2), (Outcome::IdempotentReplay, r1));
    assert_eq!(s, snap);
    let fresh = req("denied-0-retry-new-id", "A", 0, Family::Transfer, 7);
    assert_eq!(s.process(&fresh).0, Outcome::Accepted);
    assert_eq!((s.next_nonce["A"], s.balances["A"]), (1, 101));
    let m = &model()["cached_rejection"];
    assert_eq!(m["cached_auth_rejections"].as_u64().unwrap(), 1);
    assert!(!m["nonce_consumed_on_auth_rejection"].as_bool().unwrap());
}

#[test]
fn replay_with_changed_authorization_context_is_still_a_replay() {
    // Authorization is policy context, not payload identity: the cached rejection
    // is returned even if the caller now claims authorization (model rule 4).
    let mut s = State::with_principals(&["A"]);
    let mut denied = req("id-1", "A", 0, Family::Issue, 3);
    denied.authorized = false;
    s.process(&denied);
    let mut later = denied.clone();
    later.authorized = true;
    let (o, _) = s.process(&later);
    assert_eq!(o, Outcome::IdempotentReplay);
    assert_eq!(s.next_nonce["A"], 0);
}

#[test]
fn checked_arithmetic_rejects_overflow_without_writing() {
    let mut s = State::with_principals(&["A"]);
    s.balances.insert("A".into(), i64::MAX - 1);
    let before = s.clone();
    let (o, resp) = s.process(&req("ovf", "A", 0, Family::Issue, 1)); // effect +3
    assert_eq!((o, resp), (Outcome::ArithmeticRejected, None));
    assert_eq!(s, before);
    s.next_nonce.insert("A".into(), u64::MAX);
    s.balances.insert("A".into(), 0);
    let before = s.clone();
    assert_eq!(
        s.process(&req("ovf2", "A", u64::MAX, Family::Transfer, 1))
            .0,
        Outcome::ArithmeticRejected
    );
    assert_eq!(s, before);
}
