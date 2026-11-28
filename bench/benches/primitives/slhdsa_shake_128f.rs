//! SLH-DSA-SHAKE-128f: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_128f", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!("slhdsa_shake_128f", slhdsa_shake_128f, c"SLH-DSA-SHAKE-128f", 17088);
