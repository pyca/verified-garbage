//! Published RFC 5114 and NIST FFC validity vectors, vendored byte for byte
//! from cryptography with pinned provenance in vectors/sources/.
#![cfg(all(
    any(target_arch = "x86_64", target_arch = "aarch64"),
    feature = "alloc"
))]
use super::unhex;
use std::collections::BTreeMap;
use verified_garbage::ffdh::{Error, Parameters, PrivateKey, PublicKey};

fn cases(text: &str) -> Vec<BTreeMap<String, String>> {
    let mut domain = BTreeMap::new();
    let mut current = BTreeMap::new();
    let mut out = Vec::new();
    for line in text.lines() {
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let (key, value) = (key.trim(), value.trim());
        if key == "COUNT" {
            if current.contains_key("Z") {
                out.push(core::mem::take(&mut current));
            }
            current = domain.clone();
        }
        if key == "P" {
            if current.contains_key("Z") {
                out.push(core::mem::take(&mut current));
            }
            domain.clear();
        }
        if ["P", "Q", "G"].contains(&key) {
            domain.insert(key.to_string(), value.to_string());
        }
        current.insert(key.to_string(), value.to_string());
    }
    if current.contains_key("Z") {
        out.push(current);
    }
    out
}
fn hex(s: &str) -> Vec<u8> {
    unhex(s)
}
fn check(text: &str, expected: usize) {
    let vectors = cases(text);
    assert_eq!(vectors.len(), expected);
    let mut passed = 0;
    let mut failed = 0;
    for v in vectors {
        let p = hex(&v["P"]);
        let params = Parameters::from_components(&p, &hex(&v["G"]), Some(&hex(&v["Q"]))).unwrap();
        let key = PrivateKey::from_components(&params, &hex(&v["YstatIUT"]), &hex(&v["XstatIUT"]));
        let peer = PublicKey::from_components(&params, &hex(&v["YstatCAVS"]));
        let result = key.and_then(|k| k.exchange(&peer?));
        let z = hex(&v["Z"]);
        assert_eq!(z.len(), p.len());
        if v["Result"].starts_with('P') {
            assert_eq!(result, Ok(z), "COUNT {}", v["COUNT"]);
            passed += 1;
        } else {
            assert_ne!(result, Ok(z), "COUNT {}: invalid case", v["COUNT"]);
            failed += 1;
        }
    }
    assert!(passed > 0);
    if expected > 3 {
        assert!(failed > 0);
    }
}
#[test]
fn rfc5114() {
    check(
        include_str!("../../vectors/cryptography-ffdh/RFC5114/RFC5114.txt"),
        3,
    );
}
#[test]
fn nist_initiator() {
    check(
        include_str!(
            "../../vectors/cryptography-ffdh/KASValidityTest_FFCStatic_NOKC_ZZOnly_init/KASValidityTest_FFCStatic_NOKC_ZZOnly_init.fax"
        ),
        72,
    );
}
#[test]
fn nist_responder() {
    check(
        include_str!(
            "../../vectors/cryptography-ffdh/KASValidityTest_FFCStatic_NOKC_ZZOnly_resp/KASValidityTest_FFCStatic_NOKC_ZZOnly_resp.fax"
        ),
        72,
    );
}
#[test]
fn components_generation_and_padding() {
    let v = &cases(include_str!(
        "../../vectors/cryptography-ffdh/RFC5114/RFC5114.txt"
    ))[0];
    let p = hex(&v["P"]);
    let g = hex(&v["G"]);
    let q = hex(&v["Q"]);
    let params = Parameters::from_components(&p, &g, Some(&q)).unwrap();
    assert_eq!(params.components(), (&p[..], &g[..], Some(&q[..])));
    assert_eq!(params.key_size(), 1024);
    let mut padded = vec![0; 7];
    padded.extend(&p);
    assert_eq!(
        Parameters::from_components(&padded, &g, Some(&q)).unwrap(),
        params
    );
    let key = params.generate_private_key().unwrap();
    let peer = params.generate_private_key().unwrap();
    let a = key.exchange(peer.public_key()).unwrap();
    assert_eq!(a, peer.exchange(key.public_key()).unwrap());
    assert_eq!(a.len(), p.len());
    assert_eq!(key.public_key().parameters(), &params);
    let copy = PrivateKey::from_components(
        &params,
        key.public_key().component(),
        key.private_component(),
    )
    .unwrap();
    assert_eq!(copy.exchange(peer.public_key()).unwrap(), a);
    assert!(!format!("{key:?}").contains(" x:"));
    // Small exponents produce a shared integer of 16, which requires
    // modulus-width left padding. This is an algebraic property, not a KAT.
    let params = Parameters::from_components(&p, &[2], None).unwrap();
    let key = PrivateKey::from_components(&params, &[4], &[2]).unwrap();
    let z = key.exchange(key.public_key()).unwrap();
    assert_eq!(z.len(), p.len());
    assert!(z[..z.len() - 1].iter().all(|&b| b == 0));
    assert_eq!(z[z.len() - 1], 16);
}
#[test]
fn malformed_components_and_domains() {
    let v = &cases(include_str!(
        "../../vectors/cryptography-ffdh/RFC5114/RFC5114.txt"
    ))[0];
    let (p, g, q) = (hex(&v["P"]), hex(&v["G"]), hex(&v["Q"]));
    for bad_p in [vec![], vec![0; 64], vec![0x80; 63], vec![0xff; 1025]] {
        assert_eq!(
            Parameters::from_components(&bad_p, &g, None).unwrap_err(),
            Error::InvalidParameters
        );
    }
    let mut even = p.clone();
    *even.last_mut().unwrap() &= 0xfe;
    assert!(Parameters::from_components(&even, &g, None).is_err());
    for bad in [vec![], vec![1], p.clone()] {
        assert!(Parameters::from_components(&p, &bad, None).is_err());
    }
    for bad in [vec![], vec![1], vec![2], vec![4], vec![9], p.clone()] {
        assert!(Parameters::from_components(&p, &g, Some(&bad)).is_err());
    }
    assert!(Parameters::from_components(&p, &[2], Some(&q)).is_err());
    let params = Parameters::from_components(&p, &g, Some(&q)).unwrap();
    for x in [vec![], vec![0], q.clone(), p.clone()] {
        assert_eq!(
            PrivateKey::from_components(&params, &hex(&v["YstatIUT"]), &x).unwrap_err(),
            Error::InvalidKey
        );
    }
    for y in [vec![], vec![0], vec![1], vec![2], p.clone()] {
        assert_eq!(
            PublicKey::from_components(&params, &y).unwrap_err(),
            Error::InvalidKey
        );
    }
    let y = hex(&v["YstatIUT"]);
    assert_eq!(
        PrivateKey::from_components(&params, &y, &[1]).unwrap_err(),
        Error::InvalidKey
    );
    let key =
        PrivateKey::from_components(&params, &hex(&v["YstatIUT"]), &hex(&v["XstatIUT"])).unwrap();
    let other = Parameters::from_components(&p, &g, None).unwrap();
    let peer = PublicKey::from_components(&other, key.public_key().component()).unwrap();
    assert_eq!(key.exchange(&peer), Err(Error::ParametersMismatch));
    for (size, generator) in [(511, 2), (8193, 2), (512, 3)] {
        assert_eq!(
            Parameters::generate(size, generator).unwrap_err(),
            Error::InvalidParameters
        );
    }
    for error in [
        Error::InvalidParameters,
        Error::InvalidKey,
        Error::ParametersMismatch,
        Error::InvalidSharedSecret,
        Error::Randomness,
        Error::TooManyIterations,
    ] {
        assert!(!error.to_string().is_empty());
    }
}
#[test]
fn rfc3526_sizes() {
    let text = include_str!("../../vectors/cryptography-ffdh/rfc3526/rfc3526.txt");
    for (_, p) in super::fields(text).into_iter().filter(|(k, _)| *k == "P") {
        let p = hex(p);
        let params = Parameters::from_components(&p, &[2], None).unwrap();
        let k = PrivateKey::from_components(&params, &[8], &[3]).unwrap();
        let peer = PrivateKey::from_components(&params, &[128], &[7]).unwrap();
        assert_eq!(
            k.exchange(peer.public_key()).unwrap(),
            peer.exchange(k.public_key()).unwrap()
        );
        assert_eq!(params.key_size(), p.len() * 8);
    }
}

#[test]
fn safe_prime_parameter_generation() {
    for generator in [2, 5] {
        let params = Parameters::generate(512, generator).unwrap();
        assert_eq!(params.key_size(), 512);
        assert_eq!(params.components().1, &[generator as u8]);
        assert!(params.components().2.is_none());
        let key = params.generate_private_key().unwrap();
        let peer = params.generate_private_key().unwrap();
        assert_eq!(
            key.exchange(peer.public_key()).unwrap(),
            peer.exchange(key.public_key()).unwrap()
        );
    }
}
