//! Canonical request encoding v2 (checked by SIRM): request encoding v1 plus the arbiter
//! operation `resolve`. Mirrors `engineering/canonical_encoding/SPEC_request_v2.md` and the
//! independent Python reference `scripts/request_v2_reference.py`; vectors in
//! `engineering/canonical_encoding/results/request_v2_vectors.json`.
//!
//! Layout (big-endian, fixed width per tag, no optional fields):
//! `"SIRM/FTX/v2\0" (12) | request id (32) | principal u32 | nonce u64 | tag u8 | fields`.
//! Tags 0 to 9 and their fields are those of `crate::request_v1` (only the domain differs); tag 10
//! is `resolve`: escrow id `u32` and `to_beneficiary` as one byte, `0` (depositor) or `1`
//! (beneficiary). Any other byte is rejected, so every accepted input re-encodes to itself.
//! Request encoding v1 and its frozen vectors are unchanged.

use crate::integrated::{Op, Request};
use crate::request_v1 as v1;
pub use crate::request_v1::WireRequest;

pub const DOMAIN: [u8; 12] = *b"SIRM/FTX/v2\0";
const PREFIX: usize = 12 + 32 + 4 + 8 + 1;
const RESOLVE_TAG: u8 = 10;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EncodeError {
    /// An escrow id does not fit in `u32`.
    IdOutOfRange,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DecodeError {
    BadDomain,
    Truncated,
    UnknownOperation(u8),
    TrailingBytes,
    /// The `to_beneficiary` byte of `resolve` is neither 0 nor 1.
    NonCanonicalFlag(u8),
}

pub fn tag(op: &Op) -> u8 {
    v1::tag(op)
}

pub fn encode(w: &WireRequest) -> Result<Vec<u8>, EncodeError> {
    let mut out = match w.request.op {
        Op::Resolve { id, to_beneficiary } => {
            let id = u32::try_from(id).map_err(|_| EncodeError::IdOutOfRange)?;
            let mut out = Vec::with_capacity(PREFIX + 5);
            out.extend_from_slice(&DOMAIN);
            out.extend_from_slice(&w.request_id);
            out.extend_from_slice(&w.request.principal.to_be_bytes());
            out.extend_from_slice(&w.request.nonce.to_be_bytes());
            out.push(RESOLVE_TAG);
            out.extend_from_slice(&id.to_be_bytes());
            out.push(u8::from(to_beneficiary));
            return Ok(out);
        }
        _ => v1::encode(w).map_err(|e| match e {
            v1::EncodeError::IdOutOfRange => EncodeError::IdOutOfRange,
            v1::EncodeError::UnsupportedOperation => unreachable!("resolve handled above"),
        })?,
    };
    out[..12].copy_from_slice(&DOMAIN);
    Ok(out)
}

/// Total encoded length of a request with this tag; `None` for an unknown tag.
pub fn encoded_len(tag: u8) -> Option<usize> {
    if tag == RESOLVE_TAG {
        Some(PREFIX + 5)
    } else {
        v1::encoded_len(tag)
    }
}

pub fn decode(bytes: &[u8]) -> Result<WireRequest, DecodeError> {
    if bytes.len() < DOMAIN.len() || bytes[..DOMAIN.len()] != DOMAIN {
        return Err(DecodeError::BadDomain);
    }
    if bytes.len() < PREFIX {
        return Err(DecodeError::Truncated);
    }
    let tag = bytes[56];
    let need = encoded_len(tag).ok_or(DecodeError::UnknownOperation(tag))?;
    if bytes.len() < need {
        return Err(DecodeError::Truncated);
    }
    if bytes.len() > need {
        return Err(DecodeError::TrailingBytes);
    }
    if tag == RESOLVE_TAG {
        let flag = bytes[PREFIX + 4];
        if flag > 1 {
            return Err(DecodeError::NonCanonicalFlag(flag));
        }
        return Ok(WireRequest {
            request_id: bytes[12..44].try_into().unwrap(),
            request: Request {
                principal: u32::from_be_bytes(bytes[44..48].try_into().unwrap()),
                nonce: u64::from_be_bytes(bytes[48..56].try_into().unwrap()),
                op: Op::Resolve {
                    id: u32::from_be_bytes(bytes[PREFIX..PREFIX + 4].try_into().unwrap()) as usize,
                    to_beneficiary: flag == 1,
                },
            },
        });
    }
    // tags 0 to 9: identical to v1 except for the domain
    let mut as_v1 = bytes.to_vec();
    as_v1[..12].copy_from_slice(&v1::DOMAIN);
    v1::decode(&as_v1).map_err(|e| match e {
        v1::DecodeError::BadDomain => DecodeError::BadDomain,
        v1::DecodeError::Truncated => DecodeError::Truncated,
        v1::DecodeError::UnknownOperation(t) => DecodeError::UnknownOperation(t),
        v1::DecodeError::TrailingBytes => DecodeError::TrailingBytes,
    })
}
