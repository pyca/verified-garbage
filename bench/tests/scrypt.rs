//! End-to-end differential tests for scrypt's scalar mixing path.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

#[test]
fn matches_openssl() {
    // Odd r values exercise both halves of BlockMix without relying on the
    // usual r=8 workload. Small N includes j=0 and the shortest ROMix loops.
    for n in [2, 16, 1024] {
        for r in [1, 2, 3, 8, 17] {
            for p in [1, 2] {
                for len in [1, 33, 64, 100] {
                    let password: Vec<u8> = (0..73).map(|i| (i * 37 + r) as u8).collect();
                    let salt: Vec<u8> = (0..19).map(|i| (i * 11 + p) as u8).collect();
                    let mut actual = vec![0; len];
                    let mut expected = vec![0; len];
                    verified_garbage::scrypt::scrypt(
                        &password,
                        &salt,
                        n,
                        r,
                        p,
                        usize::MAX,
                        &mut actual,
                    )
                    .unwrap();
                    openssl::pkcs5::scrypt(
                        &password,
                        &salt,
                        n,
                        r.into(),
                        p.into(),
                        u64::MAX,
                        &mut expected,
                    )
                    .unwrap();
                    assert_eq!(actual, expected, "N={n} r={r} p={p} len={len}");
                }
            }
        }
    }
}
