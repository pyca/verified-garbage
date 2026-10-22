use alloc::vec;

fn power(mut x: u64, mut e: u64, modulus: u64) -> u64 {
    let mut y = 1;
    while e != 0 {
        if e & 1 != 0 {
            y = (u128::from(y) * u128::from(x) % u128::from(modulus)) as u64;
        }
        x = (u128::from(x) * u128::from(x) % u128::from(modulus)) as u64;
        e >>= 1;
    }
    y
}

fn reference(candidate: u64, witness: u64) -> bool {
    let twos = (candidate - 1).trailing_zeros();
    let mut y = power(witness % candidate, (candidate - 1) >> twos, candidate);
    if y == 1 || y == candidate - 1 {
        return true;
    }
    for _ in 1..twos {
        y = (u128::from(y) * u128::from(y) % u128::from(candidate)) as u64;
        if y == candidate - 1 {
            return true;
        }
    }
    false
}

fn check(candidate: u64, witness: u64, words: usize) {
    let stride = words + 2;
    let at = |array| 32 + array * stride;
    let mut ws = vec![0xa5a5_a5a5_a5a5_a5a5; at(28)];
    ws[6] = words as u64;
    let mut inverse = 1_u64;
    for _ in 0..6 {
        inverse = inverse.wrapping_mul(2_u64.wrapping_sub(candidate.wrapping_mul(inverse)));
    }
    ws[7] = inverse.wrapping_neg();
    for array in 0..8 {
        ws[8 + array] = ws.as_ptr() as usize as u64 + (8 * at(array)) as u64;
    }
    ws[28] = (8 * stride) as u64;
    let mut one = 1_u64;
    for _ in 0..64 * words {
        one = (u128::from(one) * 2 % u128::from(candidate)) as u64;
    }
    let twos = (candidate - 1).trailing_zeros();
    let sigma = (twos - 1) % 4 + 1;
    for (array, value) in [
        (0, candidate),
        (
            5,
            (u128::from(witness % candidate) * u128::from(one) % u128::from(candidate)) as u64,
        ),
        (9, one),
        (10, candidate - one),
        (27, (candidate - 1) >> sigma),
    ] {
        ws[at(array)..at(array) + words].fill(0);
        ws[at(array)] = value;
    }
    ws[at(27) + words] = 1_u64 << twos;
    let before = ws.clone();
    // The header, prepared Montgomery values, exponent and tail satisfy
    // the shared compact-workspace contract; the allocation remains live.
    let result =
        unsafe { crate::arch::miller_rabin::vg_miller_rabin_round(ws.as_mut_ptr(), ws.len()) };
    assert_eq!(
        result != 0,
        reference(candidate, witness),
        "c={candidate}, b={witness}, w={words}"
    );
    for (i, (&actual, &original)) in ws.iter().zip(&before).enumerate() {
        let mutable_header = [23, 26, 29, 30].contains(&i);
        let mutable_array = i >= 32 && {
            let array = (i - 32) / stride;
            [2, 3, 5, 6, 8].contains(&array) || (11..27).contains(&array)
        };
        if !mutable_header && !mutable_array {
            assert_eq!(actual, original, "protected word {i}, w={words}");
        }
    }
}

#[test]
fn prepared_round_matches_integer_arithmetic() {
    for candidate in (3..80).step_by(2) {
        for witness in 0..4 {
            check(candidate, witness, 4);
        }
    }
}

#[test]
fn prepared_round_handles_word_boundaries() {
    check(257, 2, 128);
    for words in [5, 16, 48] {
        for candidate in [257, 65537, u64::MAX - 58] {
            check(candidate, 2, words);
        }
    }
}
