//! SLH-DSA-SHAKE-256s: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_256s", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!(
    "slhdsa_shake_256s",
    slhdsa_shake_256s,
    c"SLH-DSA-SHAKE-256s",
    29792
);
