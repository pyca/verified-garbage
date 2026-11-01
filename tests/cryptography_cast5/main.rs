//! CAST5's modes of operation: pyca/cryptography's CAST5-CBC, CAST5-OFB and
//! CAST5-CFB64 vectors, vendored under `vectors/` (see `vectors/sources/`),
//! a block at a time, in pieces, and with a partial last segment; and each
//! mode against CAST5's ECB for keys of every length, whose 12 or 16 rounds
//! the vectors' 16-byte keys alone would not both reach.

#![cfg(any(
    target_arch = "x86",
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

mod cast5_cbc;
mod cast5_cfb;
mod cast5_ofb;

/// A record's key, chaining value, plaintext and ciphertext.
type Record = (Vec<u8>, [u8; 8], Vec<u8>, Vec<u8>);

/// The records of a pyca/cryptography vector file.
fn records(text: &str) -> Vec<Record> {
    let unhex = |text: &str| -> Vec<u8> {
        (0..text.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
            .collect()
    };
    text.split("\n\n")
        .filter_map(|record| {
            let field = |name: &str| {
                record
                    .lines()
                    .find_map(|l| l.strip_prefix(name)?.trim().strip_prefix('='))
                    .map(|v| unhex(v.trim()))
            };
            Some((
                field("KEY")?,
                field("IV")?.try_into().unwrap(),
                field("PLAINTEXT")?,
                field("CIPHERTEXT")?,
            ))
        })
        .collect()
}

/// Each mode agrees with CAST5's ECB, for keys of 5 to 16 bytes (12 rounds
/// up to 10 bytes, 16 beyond).
#[test]
fn modes_match_ecb() {
    use verified_garbage::cast5_cbc::Cast5Cbc;
    use verified_garbage::cast5_cfb::Cast5Cfb64;
    use verified_garbage::cast5_ecb::Cast5Ecb;
    use verified_garbage::cast5_ofb::Cast5Ofb;

    for len in 5..=16u8 {
        let key: Vec<u8> = (0..len)
            .map(|i| i.wrapping_mul(37).wrapping_add(len))
            .collect();
        let iv = [len; 8];
        let plaintext: Vec<u8> = (0..24u8).map(|i| i.wrapping_mul(91) ^ len).collect();
        let ecb = Cast5Ecb::new(&key).unwrap();
        let encrypt = |block: &[u8]| -> [u8; 8] {
            let mut b: [u8; 8] = block.try_into().unwrap();
            ecb.encrypt(&mut b).unwrap();
            b
        };
        let xor = crate::bytes::xor;

        // CBC: Cⱼ = CIPH(Pⱼ ⊕ Cⱼ₋₁); CFB64: Cⱼ = Pⱼ ⊕ CIPH(Cⱼ₋₁); OFB: Oⱼ = CIPH(Oⱼ₋₁).
        let (mut cbc, mut cfb, mut ofb) = (Vec::new(), Vec::new(), Vec::new());
        let (mut c1, mut c2, mut o) = (iv, iv, iv);
        for p in plaintext.chunks(8) {
            c1 = encrypt(&xor(p, &c1));
            cbc.extend_from_slice(&c1);
            c2 = xor(p, &encrypt(&c2)).try_into().unwrap();
            cfb.extend_from_slice(&c2);
            o = encrypt(&o);
            ofb.extend(xor(p, &o));
        }

        let mut chain = iv;
        let mut data = plaintext.clone();
        Cast5Cbc::new(&key)
            .unwrap()
            .encrypt(&mut chain, &mut data)
            .unwrap();
        assert_eq!((data.clone(), chain), (cbc.clone(), c1));
        let mut chain = iv;
        Cast5Cbc::new(&key)
            .unwrap()
            .decrypt(&mut chain, &mut data)
            .unwrap();
        assert_eq!((data, chain), (plaintext.clone(), c1));

        let cipher = Cast5Cfb64::new(&key).unwrap();
        let (mut chain, mut data) = (iv, plaintext.clone());
        cipher.encrypt(&mut chain, &mut data);
        assert_eq!((data.clone(), chain), (cfb, c2));
        let mut chain = iv;
        cipher.decrypt(&mut chain, &mut data);
        assert_eq!((data, chain), (plaintext.clone(), c2));

        let (mut chain, mut data) = (iv, plaintext.clone());
        Cast5Ofb::new(&key)
            .unwrap()
            .apply_keystream(&mut chain, &mut data);
        assert_eq!((data, chain), (ofb, o));
    }
}
