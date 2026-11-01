//! OpenSSL interoperability across supported parameter widths and generators.
#![cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[path = "../support/ffdh.rs"]
mod aws_lc;

use openssl::{
    bn::{BigNum, BigNumContext},
    dh::Dh,
};
use verified_garbage::ffdh::{Parameters, PrivateKey, PublicKey};

fn openssl_exchange(key: &Dh<openssl::pkey::Private>, peer: &[u8]) -> Vec<u8> {
    use openssl::{derive::Deriver, pkey::PKey};
    let params = || {
        Dh::from_pqg(
            key.prime_p().to_owned().unwrap(),
            key.prime_q().map(|q| q.to_owned().unwrap()),
            key.generator().to_owned().unwrap(),
        )
        .unwrap()
    };
    let private = PKey::from_dh(
        params()
            .set_key(
                key.public_key().to_owned().unwrap(),
                key.private_key().to_owned().unwrap(),
            )
            .unwrap(),
    )
    .unwrap();
    let public = PKey::from_dh(
        params()
            .set_public_key(BigNum::from_slice(peer).unwrap())
            .unwrap(),
    )
    .unwrap();
    let mut deriver = Deriver::new(&private).unwrap();
    deriver.set_peer(&public).unwrap();
    let z = deriver.derive_to_vec().unwrap();
    let mut out = vec![0; key.prime_p().num_bytes() as usize];
    let offset = out.len() - z.len();
    out[offset..].copy_from_slice(&z);
    out
}

#[test]
fn openssl_interoperability() {
    for p in [
        BigNum::get_rfc3526_prime_1536().unwrap(),
        BigNum::get_rfc3526_prime_2048().unwrap(),
        BigNum::get_rfc3526_prime_3072().unwrap(),
        BigNum::get_rfc3526_prime_4096().unwrap(),
        BigNum::get_rfc3526_prime_6144().unwrap(),
        BigNum::get_rfc3526_prime_8192().unwrap(),
    ] {
        let p = p.to_vec();
        let params = Parameters::from_components(&p, &[2], None).unwrap();
        let key = params.generate_private_key().unwrap();
        let openssl_key = Dh::from_pqg(
            BigNum::from_slice(&p).unwrap(),
            None,
            BigNum::from_u32(2).unwrap(),
        )
        .unwrap()
        .generate_key()
        .unwrap();
        let peer = PublicKey::from_components(&params, &openssl_key.public_key().to_vec()).unwrap();
        let vg_z = key.exchange(&peer).unwrap();
        let ossl_z = openssl_exchange(&openssl_key, key.public_key().component());
        assert_eq!(vg_z, ossl_z);
        let imported = PrivateKey::from_components(
            &params,
            &openssl_key.public_key().to_vec(),
            &openssl_key.private_key().to_vec(),
        )
        .unwrap();
        assert_eq!(imported.exchange(key.public_key()).unwrap(), vg_z);
        let aws_key = aws_lc::Dh::parameters(&p, &[2], None).with_key(
            &openssl_key.public_key().to_vec(),
            &openssl_key.private_key().to_vec(),
        );
        let aws_peer = aws_lc::Dh::parameters(&p, &[2], None)
            .with_key(key.public_key().component(), key.private_component());
        assert_eq!(aws_key.exchange(&aws_peer), vg_z);
        let aws_generated = aws_lc::Dh::parameters(&p, &[2], None).generate();
        // Exercise generation and padded exchange on the same domain too.
        assert_eq!(aws_generated.exchange(&aws_peer).len(), p.len());
    }
}
#[test]
fn generated_safe_primes_match_openssl_checks() {
    for generator in [2, 5] {
        let params = Parameters::generate(512, generator).unwrap();
        let (p, g, q) = params.components();
        assert!(q.is_none());
        let p = BigNum::from_slice(p).unwrap();
        let mut ctx = BigNumContext::new().unwrap();
        assert!(p.is_prime(64, &mut ctx).unwrap());
        let mut p1 = p.to_owned().unwrap();
        p1.sub_word(1).unwrap();
        let mut sophie = BigNum::new().unwrap();
        sophie.rshift1(&p1).unwrap();
        assert!(sophie.is_prime(64, &mut ctx).unwrap());
        let key = Dh::from_pqg(p, None, BigNum::from_slice(g).unwrap())
            .unwrap()
            .generate_key()
            .unwrap();
        let private = params.generate_private_key().unwrap();
        let peer = PublicKey::from_components(&params, &key.public_key().to_vec()).unwrap();
        let z = private.exchange(&peer).unwrap();
        let expected = openssl_exchange(&key, private.public_key().component());
        assert_eq!(z, expected);
    }
}

#[test]
fn partial_words_and_arbitrary_exponents_match_openssl() {
    use openssl::bn::MsbOption;
    // Moduli of many lengths from 512 to 8191 bits, whole and partial words.
    for bits in [
        512, 513, 520, 577, 960, 961, 1023, 1024, 1025, 1472, 1473, 1536, 1537, 2049, 4095, 8191,
    ] {
        let mut p = BigNum::new().unwrap();
        p.rand(bits, MsbOption::ONE, true).unwrap();
        let p_bytes = p.to_vec();
        let params = Parameters::from_components(&p_bytes, &[2], None).unwrap();
        let mut ctx = BigNumContext::new().unwrap();
        // Include every four-bit digit, in both halves of a byte.
        for exponent in [1, 2, 255, 256, 65537, 0x7654_3210, 0xfedc_ba98] {
            let x = BigNum::from_u32(exponent).unwrap();
            let mut y = BigNum::new().unwrap();
            y.mod_exp(&BigNum::from_u32(2).unwrap(), &x, &p, &mut ctx)
                .unwrap();
            let key = PrivateKey::from_components(&params, &y.to_vec(), &x.to_vec()).unwrap();
            // Importing the same exponent at different public encoding widths
            // must not change the result, including overlong zero padding.
            let wide_x = x.to_vec_padded(p_bytes.len() as i32 + 1).unwrap();
            let wide_key = PrivateKey::from_components(&params, &y.to_vec(), &wide_x).unwrap();
            let peer = PublicKey::from_components(&params, &[3]).unwrap();
            let mut z = BigNum::new().unwrap();
            z.mod_exp(&BigNum::from_u32(3).unwrap(), &x, &p, &mut ctx)
                .unwrap();
            assert_eq!(
                key.exchange(&peer).unwrap(),
                wide_key.exchange(&peer).unwrap()
            );
            assert_eq!(
                key.exchange(&peer).unwrap(),
                z.to_vec_padded(p_bytes.len() as i32).unwrap()
            );
        }
    }
}

#[test]
fn window_boundaries_match_openssl() {
    use openssl::bn::MsbOption;
    let p = BigNum::get_rfc3526_prime_2048().unwrap();
    let p_bytes = p.to_vec();
    let params = Parameters::from_components(&p_bytes, &[2], None).unwrap();
    let peer = PublicKey::from_components(&params, &[3]).unwrap();
    let mut ctx = BigNumContext::new().unwrap();
    // Exponents of 38 to 43 bytes, each at several encoded widths.
    // OpenSSL supplies an independent oracle for fresh random exponents.
    for bytes in 38..=43 {
        let mut x = BigNum::new().unwrap();
        x.rand(bytes * 8, MsbOption::ONE, false).unwrap();
        let mut y = BigNum::new().unwrap();
        y.mod_exp(&BigNum::from_u32(2).unwrap(), &x, &p, &mut ctx)
            .unwrap();
        let mut expected = BigNum::new().unwrap();
        expected
            .mod_exp(&BigNum::from_u32(3).unwrap(), &x, &p, &mut ctx)
            .unwrap();
        for padding in [0, 1, 5] {
            let encoded = x.to_vec_padded(bytes + padding).unwrap();
            let key = PrivateKey::from_components(&params, &y.to_vec(), &encoded).unwrap();
            assert_eq!(
                key.exchange(&peer).unwrap(),
                expected.to_vec_padded(256).unwrap()
            );
        }
    }
}
