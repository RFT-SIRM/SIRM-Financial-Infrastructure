//! Canonical receipt encoding v0 (proposal, not adopted). Executable reference:
//! `scripts/canonical_receipt_reference.py`; vectors:
//! `engineering/canonical_encoding/results/receipt_vectors_v0.json`.
//!
//! A receipt binds the exact request (its canonical v0 encoding, which carries the request
//! ID) to the stored response of `FinancialTransactionReceipt` (success) or
//! `FinancialTransactionDenialReceipt` (authorization / insufficient-funds denial).
//!
//! ```text
//! domain "SIRM/RCT/v0\0" (12) | status (1: 0 accepted, 1 denied) | request encoding (85 | 81)
//! accepted: accepted_nonce u64 | next_nonce u64
//! denied:   expected_nonce u64 | reason u8   (0..=4, Lean enum order)
//! ```
//!
//! The decoder enforces the Lean construction/invariants: `accepted_nonce` equals the request
//! nonce and `next_nonce = accepted_nonce + 1`; a denial's `expected_nonce` equals the request
//! nonce and its reason matches the operation family. Non-canonical input is rejected, so
//! every accepted byte string is the unique encoding of one receipt.

use crate::machine;
use crate::{decode as decode_request, encode as encode_request, DecodeError, Op, Request};

pub const DOMAIN: [u8; 12] = *b"SIRM/RCT/v0\0";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reason {
    TransferAuthorizationDenied,
    IssueAuthorizationDenied,
    BurnAuthorizationDenied,
    TransferInsufficientFunds,
    BurnInsufficientFunds,
}

impl Reason {
    pub fn code(self) -> u8 {
        match self {
            Reason::TransferAuthorizationDenied => 0,
            Reason::IssueAuthorizationDenied => 1,
            Reason::BurnAuthorizationDenied => 2,
            Reason::TransferInsufficientFunds => 3,
            Reason::BurnInsufficientFunds => 4,
        }
    }

    pub fn from_code(c: u8) -> Option<Reason> {
        Some(match c {
            0 => Reason::TransferAuthorizationDenied,
            1 => Reason::IssueAuthorizationDenied,
            2 => Reason::BurnAuthorizationDenied,
            3 => Reason::TransferInsufficientFunds,
            4 => Reason::BurnInsufficientFunds,
            _ => return None,
        })
    }

    /// `FinancialTransactionDenialReasonMatchesRequest`.
    pub fn matches(self, op: &Op) -> bool {
        matches!(
            (op, self),
            (
                Op::Transfer { .. },
                Reason::TransferAuthorizationDenied | Reason::TransferInsufficientFunds
            ) | (Op::Issue { .. }, Reason::IssueAuthorizationDenied)
                | (
                    Op::Burn { .. },
                    Reason::BurnAuthorizationDenied | Reason::BurnInsufficientFunds
                )
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Response {
    Accepted {
        accepted_nonce: u64,
        next_nonce: u64,
    },
    Denied {
        expected_nonce: u64,
        reason: Reason,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Receipt {
    pub request: Request,
    pub response: Response,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReceiptError {
    BadDomain,
    Truncated,
    TrailingBytes,
    UnknownStatus(u8),
    UnknownReason(u8),
    Request(DecodeError),
    /// `accepted_nonce` differs from the request nonce.
    AcceptedNonceMismatch,
    /// `next_nonce` is not `accepted_nonce + 1` (also: `accepted_nonce + 1` overflows u64).
    NextNonceMismatch,
    /// A denial's `expected_nonce` differs from the request nonce.
    ExpectedNonceMismatch,
    /// The denial reason does not belong to the request's operation family.
    ReasonMismatch,
}

fn check(r: &Receipt) -> Result<(), ReceiptError> {
    match r.response {
        Response::Accepted {
            accepted_nonce,
            next_nonce,
        } => {
            if accepted_nonce != r.request.nonce {
                return Err(ReceiptError::AcceptedNonceMismatch);
            }
            if accepted_nonce.checked_add(1) != Some(next_nonce) {
                return Err(ReceiptError::NextNonceMismatch);
            }
        }
        Response::Denied {
            expected_nonce,
            reason,
        } => {
            if expected_nonce != r.request.nonce {
                return Err(ReceiptError::ExpectedNonceMismatch);
            }
            if !reason.matches(&r.request.op) {
                return Err(ReceiptError::ReasonMismatch);
            }
        }
    }
    Ok(())
}

/// Encode a receipt; rejects any receipt the decoder would not accept.
pub fn encode(r: &Receipt) -> Result<Vec<u8>, ReceiptError> {
    check(r)?;
    let mut out = Vec::with_capacity(110);
    out.extend_from_slice(&DOMAIN);
    out.push(match r.response {
        Response::Accepted { .. } => 0,
        Response::Denied { .. } => 1,
    });
    out.extend_from_slice(&encode_request(&r.request));
    match r.response {
        Response::Accepted {
            accepted_nonce,
            next_nonce,
        } => {
            out.extend_from_slice(&accepted_nonce.to_be_bytes());
            out.extend_from_slice(&next_nonce.to_be_bytes());
        }
        Response::Denied {
            expected_nonce,
            reason,
        } => {
            out.extend_from_slice(&expected_nonce.to_be_bytes());
            out.push(reason.code());
        }
    }
    Ok(out)
}

pub fn decode(bytes: &[u8]) -> Result<Receipt, ReceiptError> {
    if !bytes.starts_with(&DOMAIN) {
        return Err(ReceiptError::BadDomain);
    }
    let start = DOMAIN.len() + 1;
    // domain tag 12 + request id 32 + principal 4 + nonce 8, then the operation tag.
    let tag_at = start + 12 + 32 + 4 + 8;
    if bytes.len() <= tag_at {
        return Err(ReceiptError::Truncated);
    }
    let status = bytes[DOMAIN.len()];
    if status > 1 {
        return Err(ReceiptError::UnknownStatus(status));
    }
    let req_len = match bytes[tag_at] {
        0 | 1 => 85,
        2 => 81,
        t => return Err(ReceiptError::Request(DecodeError::UnknownOperation(t))),
    };
    let end = start + req_len;
    let tail = if status == 0 { 16 } else { 9 };
    if bytes.len() < end + tail {
        return Err(ReceiptError::Truncated);
    }
    if bytes.len() > end + tail {
        return Err(ReceiptError::TrailingBytes);
    }
    let request = decode_request(&bytes[start..end]).map_err(ReceiptError::Request)?;
    let be = |at: usize| u64::from_be_bytes(bytes[at..at + 8].try_into().unwrap());
    let response = if status == 0 {
        Response::Accepted {
            accepted_nonce: be(end),
            next_nonce: be(end + 8),
        }
    } else {
        Response::Denied {
            expected_nonce: be(end),
            reason: Reason::from_code(bytes[end + 8])
                .ok_or(ReceiptError::UnknownReason(bytes[end + 8]))?,
        }
    };
    let receipt = Receipt { request, response };
    check(&receipt)?;
    Ok(receipt)
}

fn convert_op(op: &machine::Operation) -> Op {
    match *op {
        machine::Operation::Transfer {
            source,
            destination,
            asset,
            amount,
        } => Op::Transfer {
            source,
            destination,
            asset,
            amount,
        },
        machine::Operation::Issue {
            issuer,
            recipient,
            asset,
            amount,
        } => Op::Issue {
            issuer,
            recipient,
            asset,
            amount,
        },
        machine::Operation::Burn {
            holder,
            asset,
            amount,
        } => Op::Burn {
            holder,
            asset,
            amount,
        },
    }
}

fn convert_reason(r: machine::DenialReason) -> Reason {
    match r {
        machine::DenialReason::TransferAuthorizationDenied => Reason::TransferAuthorizationDenied,
        machine::DenialReason::IssueAuthorizationDenied => Reason::IssueAuthorizationDenied,
        machine::DenialReason::BurnAuthorizationDenied => Reason::BurnAuthorizationDenied,
        machine::DenialReason::TransferInsufficientFunds => Reason::TransferInsufficientFunds,
        machine::DenialReason::BurnInsufficientFunds => Reason::BurnInsufficientFunds,
    }
}

/// The receipt for a response stored by the integrated processor.
pub fn from_processor(
    id: machine::RequestId,
    request: &machine::Request,
    stored: &machine::Stored,
) -> Receipt {
    Receipt {
        request: Request {
            request_id: id,
            principal: request.principal,
            nonce: request.nonce,
            op: convert_op(&request.operation),
        },
        response: match *stored {
            machine::Stored::Accepted {
                accepted_nonce,
                next_nonce,
            } => Response::Accepted {
                accepted_nonce,
                next_nonce,
            },
            machine::Stored::Denied {
                expected_nonce,
                reason,
            } => Response::Denied {
                expected_nonce,
                reason: convert_reason(reason),
            },
        },
    }
}
