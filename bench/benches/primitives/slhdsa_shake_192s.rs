//! SLH-DSA-SHAKE-192s: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_192s", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!("slhdsa_shake_192s", slhdsa_shake_192s, c"SLH-DSA-SHAKE-192s", 16224);
