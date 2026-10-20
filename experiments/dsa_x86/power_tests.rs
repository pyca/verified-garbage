// Algebraic identities at carry-heavy moduli, not external known-answer vectors.
#[test]
fn prototype_power_carries() {
    type Pow = unsafe extern "C" fn(*mut u64, usize) -> u32;
    let powers: &[(usize, Pow)] = &[
        (3, crate::arch::dsa::proto_dsa_abi_pow_3_5),
        (4, crate::arch::dsa::proto_dsa_abi_pow_4_8),
        (16, crate::arch::dsa::proto_dsa_abi_pow_16_5),
        (32, crate::arch::dsa::proto_dsa_abi_pow_32_8),
        (48, crate::arch::dsa::proto_dsa_abi_pow_48_8),
    ];
    for &(n, power) in powers {
        let slot = |i| (64 + i * (16 * n + 8)) / 8;
        for top_shift in [0, 1, 32] {
            for magnitude in [1u64, 2] {
                for exponent in [0u64, 1, 2, 3, 15, 16, 31, 63] {
                    let mut ws = alloc::vec![0u64; slot(9)];
                    let mut modulus = alloc::vec![u64::MAX; n];
                    modulus[n - 1] >>= top_shift;
                    modulus[0] -= 58; // 2^(64*n) - 59, odd.
                    ws[slot(0)..slot(0) + n].copy_from_slice(&modulus);
                    let mut base = modulus.clone();
                    base[0] -= magnitude;
                    ws[slot(5)..slot(5) + n].copy_from_slice(&base);
                    ws[slot(8)] = exponent;
                    // SAFETY: distinct live allocations and the documented context layout.
                    assert_eq!(
                        unsafe { power(ws.as_mut_ptr(), ws.len()) },
                        0,
                        "callee-saved registers"
                    );
                    let value = if magnitude == 1 { 1 } else { 1u64 << exponent };
                    let mut expected = alloc::vec![0u64; n];
                    if exponent % 2 == 0 {
                        expected[0] = value;
                    } else {
                        expected.copy_from_slice(&modulus);
                        expected[0] -= value;
                    }
                    assert_eq!(
                        &ws[slot(6)..slot(6) + n],
                        expected,
                        "n={n} shift={top_shift} base=-{magnitude} exp={exponent}"
                    );
                }
            }
        }
    }
}
