//! Canonical request encoding v1 (proposal, not adopted): the ten operations of the integrated
//! state machine (`crate::integrated`). Mirrors `engineering/canonical_encoding/SPEC_request_v1.md`
//! and the independent Python reference `scripts/request_v1_reference.py`; vectors in
//! `engineering/canonical_encoding/results/request_v1_vectors.json`.
//!
//! Layout (big-endian, fixed width per tag, no optional fields):
//! `"SIRM/FTX/v1\0" (12) | request id (32) | principal u32 | nonce u64 | tag u8 | fields`
//! with tags 0 transfer, 1 issue, 2 burn, 3 open, 4 release, 5 cancel, 6 expire, 7 dispute,
//! 8 advance, 9 migrate.
//!
//! Escrow ids are `u32` on the wire; an id above `u32::MAX` cannot be encoded. Decoding accepts
//! exactly the canonical encodings: anything else is rejected, and every accepted input re-encodes
//! to itself. No signatures, chain id or expiry are defined here.

use crate::integrated::{Op, Request};

pub const DOMAIN: [u8; 12] = *b"SIRM/FTX/v1\0";
const PREFIX: usize = 12 + 32 + 4 + 8 + 1;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WireRequest {
    pub request_id: [u8; 32],
    pub request: Request,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncodeError {
    /// An escrow id does not fit in `u32`.
    IdOutOfRange,
    /// The operation has no wire encoding in this version (`Op::Resolve`: a later version).
    UnsupportedOperation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    BadDomain,
    Truncated,
    UnknownOperation(u8),
    TrailingBytes,
}

pub fn tag(op: &Op) -> u8 {
    match op {
        Op::Transfer { .. } => 0,
        Op::Issue { .. } => 1,
        Op::Burn { .. } => 2,
        Op::Open { .. } => 3,
        Op::Release(_) => 4,
        Op::Cancel(_) => 5,
        Op::Expire(_) => 6,
        Op::Dispute { .. } => 7,
        Op::Advance(_) => 8,
        Op::Migrate(_) => 9,
        // Reserved, not decodable: request encoding v1 has no resolve operation.
        Op::Resolve { .. } => 10,
    }
}

fn id32(id: usize) -> Result<[u8; 4], EncodeError> {
    u32::try_from(id)
        .map(u32::to_be_bytes)
        .map_err(|_| EncodeError::IdOutOfRange)
}

pub fn encode(w: &WireRequest) -> Result<Vec<u8>, EncodeError> {
    let r = &w.request;
    let mut out = Vec::with_capacity(PREFIX + 32);
    out.extend_from_slice(&DOMAIN);
    out.extend_from_slice(&w.request_id);
    out.extend_from_slice(&r.principal.to_be_bytes());
    out.extend_from_slice(&r.nonce.to_be_bytes());
    if matches!(r.op, Op::Resolve { .. }) {
        return Err(EncodeError::UnsupportedOperation);
    }
    out.push(tag(&r.op));
    let u = |out: &mut Vec<u8>, xs: &[u32]| {
        for x in xs {
            out.extend_from_slice(&x.to_be_bytes());
        }
    };
    match r.op {
        Op::Transfer {
            src,
            dst,
            asset,
            amount,
        } => {
            u(&mut out, &[src, dst, asset]);
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Issue {
            issuer,
            recipient,
            asset,
            amount,
        } => {
            u(&mut out, &[issuer, recipient, asset]);
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Burn {
            holder,
            asset,
            amount,
        } => {
            u(&mut out, &[holder, asset]);
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Open {
            id,
            depositor,
            beneficiary,
            asset,
            amount,
        } => {
            out.extend_from_slice(&id32(id)?);
            u(&mut out, &[depositor, beneficiary, asset]);
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Release(id) | Op::Cancel(id) | Op::Expire(id) => out.extend_from_slice(&id32(id)?),
        Op::Dispute { id, claimant } => {
            out.extend_from_slice(&id32(id)?);
            u(&mut out, &[claimant]);
        }
        Op::Advance(t) => out.extend_from_slice(&t.to_be_bytes()),
        Op::Migrate(amount) => out.extend_from_slice(&amount.to_be_bytes()),
        Op::Resolve { .. } => return Err(EncodeError::UnsupportedOperation),
    }
    Ok(out)
}

/// Field bytes after the prefix, by tag; `None` for an unknown tag.
fn body_len(tag: u8) -> Option<usize> {
    Some(match tag {
        0 | 1 => 28,
        2 => 24,
        3 => 32,
        4..=6 => 4,
        7 | 8 => 8,
        9 => 16,
        _ => return None,
    })
}

/// Total encoded length of a request with this tag; `None` for an unknown tag.
pub fn encoded_len(tag: u8) -> Option<usize> {
    body_len(tag).map(|b| PREFIX + b)
}

pub fn decode(bytes: &[u8]) -> Result<WireRequest, DecodeError> {
    if bytes.len() < DOMAIN.len() || bytes[..DOMAIN.len()] != DOMAIN {
        return Err(DecodeError::BadDomain);
    }
    if bytes.len() < PREFIX {
        return Err(DecodeError::Truncated);
    }
    let tag = bytes[56];
    let need = PREFIX + body_len(tag).ok_or(DecodeError::UnknownOperation(tag))?;
    if bytes.len() < need {
        return Err(DecodeError::Truncated);
    }
    if bytes.len() > need {
        return Err(DecodeError::TrailingBytes);
    }
    let u32_at = |o: usize| u32::from_be_bytes(bytes[o..o + 4].try_into().unwrap());
    let u64_at = |o: usize| u64::from_be_bytes(bytes[o..o + 8].try_into().unwrap());
    let u128_at = |o: usize| u128::from_be_bytes(bytes[o..o + 16].try_into().unwrap());
    let b = PREFIX;
    let op = match tag {
        0 => Op::Transfer {
            src: u32_at(b),
            dst: u32_at(b + 4),
            asset: u32_at(b + 8),
            amount: u128_at(b + 12),
        },
        1 => Op::Issue {
            issuer: u32_at(b),
            recipient: u32_at(b + 4),
            asset: u32_at(b + 8),
            amount: u128_at(b + 12),
        },
        2 => Op::Burn {
            holder: u32_at(b),
            asset: u32_at(b + 4),
            amount: u128_at(b + 8),
        },
        3 => Op::Open {
            id: u32_at(b) as usize,
            depositor: u32_at(b + 4),
            beneficiary: u32_at(b + 8),
            asset: u32_at(b + 12),
            amount: u128_at(b + 16),
        },
        4 => Op::Release(u32_at(b) as usize),
        5 => Op::Cancel(u32_at(b) as usize),
        6 => Op::Expire(u32_at(b) as usize),
        7 => Op::Dispute {
            id: u32_at(b) as usize,
            claimant: u32_at(b + 4),
        },
        8 => Op::Advance(u64_at(b)),
        9 => Op::Migrate(u128_at(b)),
        _ => unreachable!("tag checked by body_len"),
    };
    Ok(WireRequest {
        request_id: bytes[12..44].try_into().unwrap(),
        request: Request {
            principal: u32_at(44),
            nonce: u64_at(48),
            op,
        },
    })
}
