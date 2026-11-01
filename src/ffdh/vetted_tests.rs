//! Published RFC 3526/7919 domains exercise public policy selection. The
//! deterministic scalars below are algebraic fixtures, not external key vectors.
use super::*;
use alloc::{vec, vec::Vec};

fn unhex(text: &str) -> Vec<u8> {
    let digits: Vec<_> = text.bytes().filter(|b| b.is_ascii_hexdigit()).collect();
    digits
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let digit = |b: u8| (b as char).to_digit(16).unwrap() as u8;
            digit(pair[0]) * 16 + digit(pair[1])
        })
        .collect()
}

pub(super) fn modp_groups() -> Vec<Vec<u8>> {
    include_str!("../../vectors/cryptography-ffdh/rfc3526/rfc3526.txt")
        .lines()
        .filter_map(|line| line.strip_prefix("P = "))
        .map(unhex)
        .skip(1) // RFC 3526's 1536-bit group has no shorter-exponent policy.
        .collect()
}

fn ffdhe_groups() -> Vec<Vec<u8>> {
    include_str!("../../vectors/rfc7919/rfc7919.txt")
        .split("The hexadecimal representation of p is:")
        .skip(1)
        .map(|section| {
            let prime = section.split("The generator is:").next().unwrap();
            let words: alloc::string::String = prime
                .split_whitespace()
                .filter(|word| word.len() == 8 && word.bytes().all(|b| b.is_ascii_hexdigit()))
                .collect();
            unhex(&words)
        })
        .collect()
}

// A draw of 2^cap + 3 distinguishes truncation at the public bit cap from
// rounding the cap up to a byte, setting its high bit, or reducing modulo q.
fn marked_draw(len: usize, cap: usize) -> Vec<u8> {
    let mut draw = vec![0; len];
    draw[len - 1 - cap / 8] = 1 << (cap % 8);
    draw[len - 1] = 3;
    draw
}

fn generate_from(params: &Parameters, draw: &[u8]) -> PrivateKey {
    let mut calls = 0;
    let key = params
        .generate_with(|out| {
            calls += 1;
            assert_eq!(out.len(), params.p.len());
            assert_eq!(calls, 1, "the algebraic fixture must be accepted");
            out.copy_from_slice(draw);
            Ok::<_, ()>(())
        })
        .unwrap();
    assert_eq!(calls, 1);
    // The retained schedule is a public encoding width, even for x = 3.
    #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
    assert_eq!(key.exponent_len, params.domain.exponent_len());
    #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
    assert_eq!(
        key.exponent_len,
        params.q.as_ref().map_or(params.p.len(), Vec::len)
    );
    key
}

#[test]
fn vetted_rfc_groups_use_exact_public_bit_caps() {
    for groups in [modp_groups(), ffdhe_groups()] {
        assert_eq!(groups.len(), 5);
        for (p, cap) in groups.into_iter().zip([225, 275, 325, 375, 400]) {
            let params = Parameters::from_components(&p, &[2], None).unwrap();
            let draw = marked_draw(p.len(), cap);
            let key = generate_from(&params, &draw);
            #[cfg(any(target_arch = "arm", target_arch = "aarch64"))]
            {
                assert_eq!(key.exponent_len, cap.div_ceil(8));
                assert_eq!(canonical(key.private_component()), &[3]);
                assert_eq!(key.public_key().component(), &[8]);
            }
            #[cfg(not(any(target_arch = "arm", target_arch = "aarch64")))]
            {
                assert_eq!(key.private_component(), draw);
            }
            // The highest permitted bit must also survive: a cap one bit
            // too small would otherwise pass the truncation check above.
            let permitted = marked_draw(p.len(), cap - 1);
            assert_eq!(
                generate_from(&params, &permitted).private_component(),
                permitted
            );
        }
    }
}

#[test]
fn vetted_matching_requires_exact_prime_generator_and_subgroup() {
    let p = modp_groups().remove(0);
    let draw = marked_draw(p.len(), 225);
    let mut q = p.clone();
    *q.last_mut().unwrap() -= 1;
    let mut carry = 0;
    for byte in &mut q {
        let low = *byte & 1;
        *byte = (*byte >> 1) | (carry << 7);
        carry = low;
    }
    let absent = Parameters::from_components(&p, &[2], None).unwrap();
    let supplied = Parameters::from_components(&p, &[2], Some(&q)).unwrap();
    assert_eq!(
        generate_from(&absent, &draw).private_component(),
        generate_from(&supplied, &draw).private_component()
    );
    // Changing a single low bit of the modulus, or changing the generator,
    // must retain full sampling even when the byte width still matches.
    let mut near = p.clone();
    *near.last_mut().unwrap() -= 2;
    for params in [
        Parameters::from_components(&near, &[2], None).unwrap(),
        Parameters::from_components(&p, &[5], None).unwrap(),
    ] {
        assert_eq!(generate_from(&params, &draw).private_component(), draw);
    }
    *q.last_mut().unwrap() -= 2;
    assert_eq!(
        Parameters::from_components(&p, &[2], Some(&q)),
        Err(Error::InvalidParameters)
    );
}

#[test]
fn vetted_generation_preserves_entropy_refills() {
    let p = modp_groups().remove(0);
    let params = Parameters::from_components(&p, &[2], None).unwrap();
    let mut calls = 0;
    let key = params
        .generate_with(|out| {
            calls += 1;
            assert_eq!(out.len(), p.len());
            out.fill(0);
            if calls == 2 {
                *out.last_mut().unwrap() = 3;
            }
            Ok::<_, ()>(())
        })
        .unwrap();
    assert_eq!(calls, 2);
    assert_eq!(canonical(key.private_component()), &[3]);
    assert_eq!(key.public_key().component(), &[8]);
    // A single tape can contain both a rejected and an accepted draw. The
    // second starts at p_len, even when the scalar schedule is shorter.
    let mut tape = vec![0; 2 * p.len()];
    *tape.last_mut().unwrap() = 3;
    let mut state = params.domain.key_state();
    let (mut x, mut y) = (vec![0xa5; p.len()], vec![0x5a; p.len()]);
    assert_eq!(
        params.domain.key_search(&mut state, &tape, &mut x, &mut y),
        (1, 2 * p.len(), 0)
    );
    assert_eq!(canonical(&x), &[3]);
    assert_eq!(canonical(&y), &[8]);
    assert_eq!(&state[..2], &[0, 0]);
    let mut calls = 0;
    assert_eq!(
        params
            .generate_with(|out| {
                calls += 1;
                assert_eq!(out.len(), p.len());
                out.fill(0);
                if calls == 1 { Ok(()) } else { Err(()) }
            })
            .unwrap_err(),
        Error::Randomness
    );
    assert_eq!(calls, 2);
}

#[cfg(any(
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "powerpc64"
))]
#[test]
fn vetted_domain_validation_checks_complete_components() {
    for p in modp_groups().into_iter().chain(ffdhe_groups()) {
        // The subgroup order is derived from the published safe prime.
        let mut q = p.clone();
        *q.last_mut().unwrap() -= 1;
        let mut carry = 0;
        for byte in &mut q {
            let low = *byte & 1;
            *byte = (*byte >> 1) | (carry << 7);
            carry = low;
        }
        for order in [None, Some(q.as_slice())] {
            let params = Parameters::from_components(&p, &[2], order).unwrap();
            assert_eq!(params.components(), (p.as_slice(), &[2][..], order));
        }
        let mut even_order = q.clone();
        *even_order.last_mut().unwrap() ^= 1;
        assert_eq!(
            Parameters::from_components(&p, &[2], Some(&even_order)).unwrap_err(),
            Error::InvalidParameters
        );
        let mut different_prime = p.clone();
        *different_prime.last_mut().unwrap() -= 2;
        assert_eq!(
            Parameters::from_components(&different_prime, &[2], Some(&q)).unwrap_err(),
            Error::InvalidParameters
        );
        assert_eq!(
            Parameters::from_components(&p, &[1], Some(&q)).unwrap_err(),
            Error::InvalidParameters
        );
        // A nonmatching but valid generator must reach the general validator.
        // Squaring the published generator keeps it in the same subgroup.
        assert!(Parameters::from_components(&p, &[4], Some(&q)).is_ok());
    }
}
