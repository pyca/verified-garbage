//! SLH-DSA-SHAKE-128s: key generation, signing and verification, beside
//! OpenSSL (see `slhdsa.rs`).

pub const USES: &[&str] = &["slhdsa_shake_128s", "slhdsa_common", "sha3"];

super::slhdsa::slhdsa_bench!(
    "slhdsa_shake_128s",
    slhdsa_shake_128s,
    c"SLH-DSA-SHAKE-128s",
    7856
);
