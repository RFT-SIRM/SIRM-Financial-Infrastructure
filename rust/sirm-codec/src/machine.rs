//! Integrated transaction processor: holdings (`ledger`) + static authorization
//! (`auth`) + request-ID idempotency and per-principal nonces, following the Lean
//! `SIRM.FinancialTransactionEnvelope` / `SIRM.FinancialTransactionDenials` policy.
//!
//! Order of checks for one request `(id, request)`:
//! 1. Lookup of `id` in the shared receipt/denial cache. Same request: replay the stored
//!    response. Different request: `RequestIdConflict`. Nothing is written.
//! 2. The nonce must equal the principal's next nonce; otherwise `StaleNonce` /
//!    `FutureNonce`, nothing written, nothing cached.
//! 3. Authorization failure: cache a denial, consume no nonce, no financial effect.
//! 4. Authorized but unfunded non-self transfer or burn: cache a funds denial likewise.
//! 5. Otherwise the ledger operation, the nonce increment and the receipt commit together.
//!
//! Not modelled (also absent from this Rust layer): the Lean general-ledger mirror,
//! signatures, expiry, persistence, concurrency. Ledger-range errors (unknown account or
//! asset, arithmetic overflow) have no Lean counterpart; they are returned as
//! `Invalid` with no write and no cache entry.

use crate::auth::{AuthError, Policy};
use crate::ledger::{Holdings, LedgerError};
use std::collections::BTreeMap;

pub type RequestId = [u8; 32];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    Transfer {
        source: u32,
        destination: u32,
        asset: u32,
        amount: u128,
    },
    Issue {
        issuer: u32,
        recipient: u32,
        asset: u32,
        amount: u128,
    },
    Burn {
        holder: u32,
        asset: u32,
        amount: u128,
    },
}

/// The exact typed payload; the request ID travels separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Request {
    pub principal: u32,
    pub nonce: u64,
    pub operation: Operation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DenialReason {
    TransferAuthorizationDenied,
    IssueAuthorizationDenied,
    BurnAuthorizationDenied,
    TransferInsufficientFunds,
    BurnInsufficientFunds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stored {
    Accepted {
        accepted_nonce: u64,
        next_nonce: u64,
    },
    Denied {
        expected_nonce: u64,
        reason: DenialReason,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// New success committed.
    Accepted(Stored),
    /// New denial cached.
    DeniedCached(Stored),
    /// Exact retry: the stored response, unchanged.
    Replay(Stored),
    RequestIdConflict,
    StaleNonce,
    FutureNonce,
    /// Ledger-range or arithmetic failure; nothing written or cached.
    Invalid(LedgerError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Processor {
    pub ledger: Holdings,
    policy: Policy,
    next_nonce: BTreeMap<u32, u64>,
    cache: BTreeMap<RequestId, (Request, Stored)>,
}

impl Processor {
    pub fn new(ledger: Holdings, policy: Policy) -> Processor {
        Processor {
            ledger,
            policy,
            next_nonce: BTreeMap::new(),
            cache: BTreeMap::new(),
        }
    }

    pub fn next_nonce(&self, principal: u32) -> u64 {
        self.next_nonce.get(&principal).copied().unwrap_or(0)
    }

    pub fn cached(&self) -> usize {
        self.cache.len()
    }

    pub fn process(&mut self, id: RequestId, req: Request) -> Outcome {
        if let Some((prior, stored)) = self.cache.get(&id) {
            return if *prior == req {
                Outcome::Replay(*stored)
            } else {
                Outcome::RequestIdConflict
            };
        }
        let expected = self.next_nonce(req.principal);
        if req.nonce < expected {
            return Outcome::StaleNonce;
        }
        if req.nonce > expected {
            return Outcome::FutureNonce;
        }
        // Every fallible step precedes the first write of nonce/cache.
        let Some(next) = expected.checked_add(1) else {
            return Outcome::Invalid(LedgerError::Overflow);
        };

        let p = req.principal;
        let (result, auth_reason, funds_reason) = match req.operation {
            Operation::Transfer {
                source,
                destination,
                asset,
                amount,
            } => (
                self.policy
                    .transfer(&mut self.ledger, p, source, destination, asset, amount),
                DenialReason::TransferAuthorizationDenied,
                DenialReason::TransferInsufficientFunds,
            ),
            Operation::Issue {
                issuer,
                recipient,
                asset,
                amount,
            } => (
                self.policy
                    .issue(&mut self.ledger, p, issuer, recipient, asset, amount),
                DenialReason::IssueAuthorizationDenied,
                DenialReason::IssueAuthorizationDenied, // unreachable: issuance has no funds denial
            ),
            Operation::Burn {
                holder,
                asset,
                amount,
            } => (
                self.policy.burn(&mut self.ledger, p, holder, asset, amount),
                DenialReason::BurnAuthorizationDenied,
                DenialReason::BurnInsufficientFunds,
            ),
        };

        match result {
            Ok(()) => {
                let stored = Stored::Accepted {
                    accepted_nonce: req.nonce,
                    next_nonce: next,
                };
                self.next_nonce.insert(p, next);
                self.cache.insert(id, (req, stored));
                Outcome::Accepted(stored)
            }
            Err(AuthError::Unauthorized) => self.deny(id, req, expected, auth_reason),
            Err(AuthError::Ledger(LedgerError::Insufficient)) => {
                self.deny(id, req, expected, funds_reason)
            }
            Err(AuthError::Ledger(e)) => Outcome::Invalid(e),
        }
    }

    fn deny(
        &mut self,
        id: RequestId,
        req: Request,
        expected: u64,
        reason: DenialReason,
    ) -> Outcome {
        let stored = Stored::Denied {
            expected_nonce: expected,
            reason,
        };
        self.cache.insert(id, (req, stored));
        Outcome::DeniedCached(stored)
    }
}
