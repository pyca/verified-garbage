//! The RSADP component vectors of SP 800-56B (vectors/nist-cavp-rsadp/):
//! their exponents, random numbers about as long as their moduli, are all
//! beyond BoringSSL's limits (odd, from 3 to `2^33 - 1`), which the public
//! key enforces, so each key is refused.

#![cfg(all(target_arch = "x86_64", feature = "alloc"))]

use verified_garbage::rsa::{Error, PublicKey};

use super::unhex;

#[test]
fn rsadp_component() {
    let text = include_str!("../../vectors/nist-cavp-rsadp/RSADPComponent800_56B.rsp");
    let mut count = 0;
    for v in text.split("COUNT = ").skip(1) {
        let field = |name: &str| {
            v.lines()
                .find_map(|l| l.split_once(" = ").filter(|(k, _)| k.trim() == name))
                .map(|(_, x)| x.trim())
        };
        let n = unhex(field("n").unwrap());
        // NIST writes the exponent as a number, in an odd number of digits
        // when its top byte is below 0x10.
        let e = field("e").unwrap();
        let e = unhex(&format!("{}{e}", "0".repeat(e.len() % 2)));
        assert!(e.len() > 5);
        assert_eq!(PublicKey::new(&n, &e), Err(Error::InvalidExponent));
        count += 1;
    }
    assert_eq!(count, 60);
}
