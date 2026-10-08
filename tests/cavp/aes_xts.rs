//! NIST CAVP XTS-AES vectors (`XTSGenAES128.rsp`, `XTSGenAES256.rsp`), with
//! unmodified sources under vectors/.
//!
//! The files also test data units that are not whole bytes (130, 140 and
//! 250 bits), which the crate does not support; every vector of whole bytes
//! is checked, in both directions.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86"
))]

use std::collections::BTreeMap;

use verified_garbage::aes_xts::{AesXts, Error, MAX_BLOCKS};

use super::unhex;

/// Checks every vector of whole bytes of a response file, in both
/// directions, and returns how many there were and how many were skipped.
fn check_file(text: &str) -> (usize, usize) {
    let (mut count, mut skipped) = (0, 0);
    for record in text.replace('\r', "").split("\n\n") {
        let fields: BTreeMap<_, _> = record
            .lines()
            .filter_map(|line| line.trim().split_once(" = "))
            .collect();
        if !fields.contains_key("COUNT") {
            continue;
        }
        let bits: usize = fields["DataUnitLen"].parse().unwrap();
        if !bits.is_multiple_of(8) {
            skipped += 1;
            continue;
        }
        let (pt, ct) = (unhex(fields["PT"]), unhex(fields["CT"]));
        assert_eq!(pt.len() * 8, bits);
        let ctx = AesXts::new(&unhex(fields["Key"])).unwrap();
        let i: [u8; 16] = unhex(fields["i"]).try_into().unwrap();
        let mut buffer = pt.clone();
        ctx.encrypt(&i, &mut buffer).unwrap();
        assert_eq!(buffer, ct);
        ctx.decrypt(&i, &mut buffer).unwrap();
        assert_eq!(buffer, pt);
        count += 1;
    }
    (count, skipped)
}

#[test]
fn nist_xts() {
    let files = [
        (
            include_str!("../../vectors/nist-cavp-aes-xts/XTSGenAES128.rsp"),
            (800, 200),
        ),
        (
            include_str!("../../vectors/nist-cavp-aes-xts/XTSGenAES256.rsp"),
            (600, 400),
        ),
    ];
    for (text, expected) in files {
        assert_eq!(check_file(text), expected);
    }
}

#[test]
fn limits_and_lengths() {
    for len in 0..=80 {
        let key: Vec<_> = (0..len).map(|i| (17 * i + 3) as u8).collect();
        if !matches!(len, 32 | 48 | 64) {
            assert!(matches!(AesXts::new(&key), Err(Error::InvalidKeyLength)));
            continue;
        }
        let mut equal = key.clone();
        equal.copy_within(..len / 2, len / 2);
        assert!(matches!(AesXts::new(&equal), Err(Error::EqualKeyHalves)));
        let ctx = AesXts::new(&key).unwrap();
        let i = [0x3c; 16];
        for n in 0..16 {
            let mut buffer = vec![0x5a; n];
            assert_eq!(ctx.encrypt(&i, &mut buffer), Err(Error::DataUnitTooShort));
            assert_eq!(ctx.decrypt(&i, &mut buffer), Err(Error::DataUnitTooShort));
            assert_eq!(buffer, [0x5a; 16][..n]);
        }
        // Every length round-trips, and a data unit's whole blocks before
        // the last two do not depend on what follows them.
        let message: Vec<_> = (0..16 * 6).map(|i| (7 * i + 1) as u8).collect();
        let mut whole = message.clone();
        ctx.encrypt(&i, &mut whole).unwrap();
        for n in 16..=message.len() {
            let mut buffer = message[..n].to_vec();
            ctx.encrypt(&i, &mut buffer).unwrap();
            let settled = (n / 16).saturating_sub(1) * 16;
            assert_eq!(buffer[..settled], whole[..settled]);
            if n % 16 == 0 {
                assert_eq!(buffer, whole[..n]);
            }
            ctx.decrypt(&i, &mut buffer).unwrap();
            assert_eq!(buffer, message[..n]);
        }
    }
    let ctx = AesXts::new(&[[1; 16], [2; 16]].concat()).unwrap();
    let mut buffer = vec![0; 16 * MAX_BLOCKS + 1];
    assert_eq!(
        ctx.encrypt(&[0; 16], &mut buffer),
        Err(Error::DataUnitTooLong)
    );
    assert_eq!(
        ctx.decrypt(&[0; 16], &mut buffer),
        Err(Error::DataUnitTooLong)
    );
    assert!(buffer.iter().all(|&b| b == 0));
}
