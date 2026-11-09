//! X448 (`XdhComp` vectors of `x448_test.json`).
//!
//! Every vector, valid or acceptable, has the shared secret RFC 7748's
//! X448 computes, which [`PrivateKey::exchange`] must return, but for the
//! all-zero shared secrets, which it rejects. The acceptable ones are public
//! keys of small order (whose shared secret is all zero), and public keys on
//! the twist or not reduced modulo p, which RFC 7748 processes like any
//! other. Oversized public keys fail conversion to the API's
//! fixed-size byte array.

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "x86",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "riscv64",
    all(target_arch = "powerpc64", target_endian = "little")
))]

use verified_garbage::error::XdhError;
use verified_garbage::x448::{PrivateKey, PublicKey};

use super::harness::{self, Count, Expectation};
use super::schema::{CurveGroup, EcdhCase};
use crate::require_vectors;

#[test]
fn x448_test() {
    require_vectors!();
    let file = harness::load::<CurveGroup, EcdhCase>("x448_test.json");
    let checked = Count::default();
    file.par_tests(|group, test| {
        assert_eq!(group.params.curve, "curve448");
        checked.add();
        let public: Result<[u8; 56], _> = test.case.public.0.clone().try_into();
        let public = match public {
            Ok(public) => public,
            Err(_) => {
                assert_eq!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
                return;
            }
        };
        assert_ne!(test.result, Expectation::Invalid, "tcId {}", test.tc_id);
        let private: [u8; 56] = test.case.private.0.clone().try_into().unwrap();
        let shared: [u8; 56] = test.case.shared.0.clone().try_into().unwrap();
        let expected = if shared == [0; 56] {
            Err(XdhError::ZeroSharedSecret)
        } else {
            Ok(shared)
        };
        let key = PrivateKey::from_bytes(&private);
        let got = key.exchange(&PublicKey::from_bytes(&public));
        assert_eq!(got, expected, "tcId {}", test.tc_id);
    });
    assert!(checked.get() > 0);
}
