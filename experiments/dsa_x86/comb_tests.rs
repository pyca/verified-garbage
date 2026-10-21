#[test]
fn prototype_comb_reuse() {
    type Pow = unsafe extern "C" fn(*mut u64, usize) -> u32;
    let powers: &[(usize, usize, Pow, Pow, Pow)] = &[
        (
            16,
            5,
            crate::arch::dsa::proto_dsa_abi_comb_build_16_5,
            crate::arch::dsa::proto_dsa_abi_comb_power_16_5,
            crate::arch::dsa::proto_dsa_abi_pow_16_5,
        ),
        (
            32,
            5,
            crate::arch::dsa::proto_dsa_abi_comb_build_32_5,
            crate::arch::dsa::proto_dsa_abi_comb_power_32_5,
            crate::arch::dsa::proto_dsa_abi_pow_32_5,
        ),
        (
            32,
            7,
            crate::arch::dsa::proto_dsa_abi_comb_build_32_7,
            crate::arch::dsa::proto_dsa_abi_comb_power_32_7,
            crate::arch::dsa::proto_dsa_abi_pow_32_7,
        ),
        (
            32,
            8,
            crate::arch::dsa::proto_dsa_abi_comb_build_32_8,
            crate::arch::dsa::proto_dsa_abi_comb_power_32_8,
            crate::arch::dsa::proto_dsa_abi_pow_32_8,
        ),
        (
            48,
            8,
            crate::arch::dsa::proto_dsa_abi_comb_build_48_8,
            crate::arch::dsa::proto_dsa_abi_comb_power_48_8,
            crate::arch::dsa::proto_dsa_abi_pow_48_8,
        ),
    ];
    for &(n, e, prepare, power, reference) in powers {
        let slot = |i| (64 + i * (16 * n + 8)) / 8;
        for negative in [false, true] {
            let mut ws = alloc::vec![0u64; 128*n];
            let mut modulus = alloc::vec![u64::MAX; n];
            modulus[0] -= 58;
            ws[slot(0)..slot(0) + n].copy_from_slice(&modulus);
            if negative {
                ws[slot(5)..slot(5) + n].copy_from_slice(&modulus);
                ws[slot(5)] -= 2;
            } else {
                ws[slot(5)] = 2;
            }
            let initial = ws.clone();
            for (exponent, call) in [(23, prepare), (59, power)] {
                ws[slot(8)] = exponent;
                // SAFETY: the context and persistent table fit in the live scratch allocation.
                assert_eq!(
                    unsafe { call(ws.as_mut_ptr(), ws.len()) },
                    0,
                    "callee-saved registers"
                );
                let mut expected = alloc::vec![0u64; n];
                if negative {
                    expected.copy_from_slice(&modulus);
                    expected[0] -= 1u64 << exponent;
                } else {
                    expected[0] = 1u64 << exponent;
                }
                assert_eq!(
                    &ws[slot(6)..slot(6) + n],
                    expected,
                    "n={n} negative={negative} exponent={exponent}"
                );
                // Shape checks may destroy the arithmetic context between the two calls.
                ws[..slot(9)].fill(0);
                ws[slot(0)..slot(0) + n].copy_from_slice(&modulus);
            }
            // Exercise all exponent columns, including the high padded boundary.
            for pattern in [0xa5a5a5a5u64, 0xffffffff] {
                for call in [prepare, power] {
                    ws[..slot(9)].copy_from_slice(&initial[..slot(9)]);
                    for i in 0..e {
                        ws[slot(8) + i / 2] |= pattern << (32 * (i % 2));
                    }
                    let mut expected = ws.clone();
                    // SAFETY: both scratch allocations cover their respective contexts.
                    assert_eq!(
                        unsafe { reference(expected.as_mut_ptr(), expected.len()) },
                        0
                    );
                    assert_eq!(unsafe { call(ws.as_mut_ptr(), ws.len()) }, 0);
                    assert_eq!(
                        &ws[slot(6)..slot(6) + n],
                        &expected[slot(6)..slot(6) + n],
                        "dense exponent n={n} e={e}"
                    );
                }
            }
        }
    }
}
