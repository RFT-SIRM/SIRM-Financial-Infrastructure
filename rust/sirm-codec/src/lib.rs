//! Canonical request encoding v0 (proposal). Mirrors
//! `engineering/canonical_encoding/SPEC_v0.md` and the Python reference
//! `scripts/canonical_encoding_reference.py`. Conformance is checked against
//! `engineering/canonical_encoding/results/vectors_v0.json`.
//!
//! Not a production transaction processor: no signatures, expiry, chain id,
//! or response encoding. Field widths are fixed Rust integer types, so
//! out-of-range values cannot be constructed; range rejection happens when a
//! value is parsed into these types.
#![forbid(unsafe_code)]

pub mod auth;
pub mod dispute;
pub mod envelope;
pub mod escrow;
pub mod fees;
pub mod ledger;
pub mod machine;
pub mod timelock;

use sha2::{Digest, Sha256};

pub const DOMAIN: [u8; 12] = *b"SIRM/FTX/v0\0";

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Request {
    pub request_id: [u8; 32],
    pub principal: u32,
    pub nonce: u64,
    pub op: Op,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecodeError {
    BadDomain,
    Truncated,
    UnknownOperation(u8),
    TrailingBytes,
}

pub fn encode(r: &Request) -> Vec<u8> {
    let mut out = Vec::with_capacity(85);
    out.extend_from_slice(&DOMAIN);
    out.extend_from_slice(&r.request_id);
    out.extend_from_slice(&r.principal.to_be_bytes());
    out.extend_from_slice(&r.nonce.to_be_bytes());
    match &r.op {
        Op::Transfer {
            source,
            destination,
            asset,
            amount,
        } => {
            out.push(0);
            for v in [source, destination, asset] {
                out.extend_from_slice(&v.to_be_bytes());
            }
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Issue {
            issuer,
            recipient,
            asset,
            amount,
        } => {
            out.push(1);
            for v in [issuer, recipient, asset] {
                out.extend_from_slice(&v.to_be_bytes());
            }
            out.extend_from_slice(&amount.to_be_bytes());
        }
        Op::Burn {
            holder,
            asset,
            amount,
        } => {
            out.push(2);
            for v in [holder, asset] {
                out.extend_from_slice(&v.to_be_bytes());
            }
            out.extend_from_slice(&amount.to_be_bytes());
        }
    }
    out
}

struct Reader<'a> {
    b: &'a [u8],
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], DecodeError> {
        if self.b.len() < n {
            return Err(DecodeError::Truncated);
        }
        let (h, t) = self.b.split_at(n);
        self.b = t;
        Ok(h)
    }
    fn u32(&mut self) -> Result<u32, DecodeError> {
        Ok(u32::from_be_bytes(self.take(4)?.try_into().unwrap()))
    }
    fn u64(&mut self) -> Result<u64, DecodeError> {
        Ok(u64::from_be_bytes(self.take(8)?.try_into().unwrap()))
    }
    fn u128(&mut self) -> Result<u128, DecodeError> {
        Ok(u128::from_be_bytes(self.take(16)?.try_into().unwrap()))
    }
}

pub fn decode(bytes: &[u8]) -> Result<Request, DecodeError> {
    let mut r = Reader { b: bytes };
    if r.take(DOMAIN.len()).map_err(|_| DecodeError::BadDomain)? != DOMAIN {
        return Err(DecodeError::BadDomain);
    }
    let request_id: [u8; 32] = r.take(32)?.try_into().unwrap();
    let principal = r.u32()?;
    let nonce = r.u64()?;
    let tag = r.take(1)?[0];
    let op = match tag {
        0 => Op::Transfer {
            source: r.u32()?,
            destination: r.u32()?,
            asset: r.u32()?,
            amount: r.u128()?,
        },
        1 => Op::Issue {
            issuer: r.u32()?,
            recipient: r.u32()?,
            asset: r.u32()?,
            amount: r.u128()?,
        },
        2 => Op::Burn {
            holder: r.u32()?,
            asset: r.u32()?,
            amount: r.u128()?,
        },
        t => return Err(DecodeError::UnknownOperation(t)),
    };
    if !r.b.is_empty() {
        return Err(DecodeError::TrailingBytes);
    }
    Ok(Request {
        request_id,
        principal,
        nonce,
        op,
    })
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}
