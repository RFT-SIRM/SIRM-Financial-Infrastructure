//! Rust port of the finite transaction-envelope policy modelled in
//! `scripts/model_check_transaction_envelope.py` and documented in
//! `engineering/transaction_envelope/MODEL_SCOPE.md`.
//!
//! Policy (identical to the Python model):
//! 1. Existing request ID with the same payload: return the stored response, no write.
//! 2. Existing request ID with a different payload: `RequestIdConflict`, no write.
//! 3. Nonce below/above the principal's expected nonce: `StaleNonce` / `FutureNonce`,
//!    no write, nothing cached.
//! 4. Deterministic authorization rejection: cache the rejection under the ID and
//!    payload; consume no nonce; no financial effect.
//! 5. Success: balance effect, nonce increment and receipt are written together.
//!
//! Atomicity here is by construction: every check happens before the first write,
//! and no fallible step follows a write. This is a single-threaded reference of the
//! transition, not a concurrent or durable store.
//!
//! One deliberate extension over the Python model: balance arithmetic is checked.
//! An overflowing effect is rejected as `ArithmeticRejected` with no write and no
//! cache entry. The Python model uses unbounded integers and has no such case.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Family {
    Transfer,
    Issue,
    Burn,
}

impl Family {
    /// Synthetic one-account effect used only to distinguish winners (as in the model).
    pub fn effect(self) -> i64 {
        match self {
            Family::Transfer => 1,
            Family::Issue => 3,
            Family::Burn => -2,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    pub request_id: String,
    pub principal: String,
    pub nonce: u64,
    pub family: Family,
    pub amount: u64,
    /// Policy context, not part of the payload identity.
    pub authorized: bool,
}

/// Exact payload identity: authorization context and request ID are excluded.
pub type Payload = (String, u64, Family, u64);

impl Request {
    pub fn payload(&self) -> Payload {
        (self.principal.clone(), self.nonce, self.family, self.amount)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResponseCode {
    Accepted,
    AuthorizationRejected,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Response {
    pub code: ResponseCode,
    pub request_id: String,
    pub accepted_nonce: Option<u64>,
    pub next_nonce: Option<u64>,
    pub balance_after: Option<i64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Accepted,
    AuthorizationRejectedCached,
    IdempotentReplay,
    RequestIdConflict,
    StaleNonce,
    FutureNonce,
    /// Extension: checked balance arithmetic failed; nothing written or cached.
    ArithmeticRejected,
}

pub const INITIAL_BALANCE: i64 = 100;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct State {
    pub next_nonce: BTreeMap<String, u64>,
    pub balances: BTreeMap<String, i64>,
    pub receipts: BTreeMap<String, (Payload, Response)>,
    pub commits: BTreeMap<String, u64>,
}

impl State {
    pub fn with_principals(principals: &[&str]) -> State {
        let mut s = State::default();
        for p in principals {
            s.next_nonce.insert((*p).to_string(), 0);
            s.balances.insert((*p).to_string(), INITIAL_BALANCE);
        }
        s
    }

    pub fn commit_total(&self) -> u64 {
        self.commits.values().sum()
    }

    /// Process one request at a linearization point.
    pub fn process(&mut self, req: &Request) -> (Outcome, Option<Response>) {
        if let Some((prior_payload, prior_response)) = self.receipts.get(&req.request_id) {
            if *prior_payload == req.payload() {
                return (Outcome::IdempotentReplay, Some(prior_response.clone()));
            }
            return (Outcome::RequestIdConflict, None);
        }

        let expected = self.next_nonce.get(&req.principal).copied().unwrap_or(0);
        if req.nonce < expected {
            return (Outcome::StaleNonce, None);
        }
        if req.nonce > expected {
            return (Outcome::FutureNonce, None);
        }

        if !req.authorized {
            let response = Response {
                code: ResponseCode::AuthorizationRejected,
                request_id: req.request_id.clone(),
                accepted_nonce: None,
                next_nonce: Some(expected),
                balance_after: None,
            };
            self.receipts
                .insert(req.request_id.clone(), (req.payload(), response.clone()));
            return (Outcome::AuthorizationRejectedCached, Some(response));
        }

        // All fallible steps first; writes only after every check has passed.
        let old_balance = self
            .balances
            .get(&req.principal)
            .copied()
            .unwrap_or(INITIAL_BALANCE);
        let Some(new_balance) = old_balance.checked_add(req.family.effect()) else {
            return (Outcome::ArithmeticRejected, None);
        };
        let Some(next) = expected.checked_add(1) else {
            return (Outcome::ArithmeticRejected, None);
        };

        let response = Response {
            code: ResponseCode::Accepted,
            request_id: req.request_id.clone(),
            accepted_nonce: Some(req.nonce),
            next_nonce: Some(next),
            balance_after: Some(new_balance),
        };
        self.balances.insert(req.principal.clone(), new_balance);
        self.next_nonce.insert(req.principal.clone(), next);
        self.receipts
            .insert(req.request_id.clone(), (req.payload(), response.clone()));
        *self.commits.entry(req.request_id.clone()).or_insert(0) += 1;
        (Outcome::Accepted, Some(response))
    }
}
