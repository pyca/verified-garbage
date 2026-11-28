//! SLH-DSA-SHAKE-256f: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_256f", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!("slhdsa_shake_256f", slhdsa_shake_256f, c"SLH-DSA-SHAKE-256f", 49856);
