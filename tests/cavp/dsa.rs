//! Every published FIPS 186-4 DSA verification vector, at all four widths.
#![cfg(all(
    any(
        target_arch = "x86",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "arm",
        all(target_arch = "powerpc64", target_endian = "little")
    ),
    feature = "alloc"
))]

use verified_garbage::dsa::PublicKey;
use verified_garbage::hashes::{
    sha1::Sha1, sha224::Sha224, sha256::Sha256, sha384::Sha384, sha512::Sha512,
};

#[path = "dsa_vectors.rs"]
mod vectors;
use vectors::{hex, vectors};

#[test]
fn signatures() {
    for (i, v) in vectors(
        &crate::vectors::text("vectors/nist-cavp-dsa/SigVer.rsp"),
        false,
    )
    .iter()
    .enumerate()
    {
        let p = hex(&v["P"], 0);
        let q = hex(&v["Q"], 0);
        let key =
            PublicKey::from_components(&p, &q, &hex(&v["G"], p.len()), &hex(&v["Y"], p.len()))
                .unwrap();
        let msg = hex(&v["Msg"], 0);
        let hashes: [(&str, Vec<u8>); 5] = [
            ("SHA-1", Sha1::digest(&msg).to_vec()),
            ("SHA-224", Sha224::digest(&msg).to_vec()),
            ("SHA-256", Sha256::digest(&msg).to_vec()),
            ("SHA-384", Sha384::digest(&msg).to_vec()),
            ("SHA-512", Sha512::digest(&msg).to_vec()),
        ];
        let digest = &hashes
            .iter()
            .find(|(name, _)| *name == v["Hash"])
            .unwrap()
            .1;
        let signature = [hex(&v["R"], q.len()), hex(&v["S"], q.len())].concat();
        let actual = key.verify(digest, &signature);
        let expected = v["Result"].starts_with('P');
        assert_eq!(actual, expected, "vector {i}");
    }
}
