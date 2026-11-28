//! SLH-DSA-SHAKE-192f: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_192f", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!("slhdsa_shake_192f", slhdsa_shake_192f, c"SLH-DSA-SHAKE-192f", 35664);
