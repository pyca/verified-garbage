//! AES-CCM: every vector of the CCM files, generation-encryption varying the
//! length of the associated data (`VADT`), of the nonce (`VNT`), of the
//! payload (`VPT`) and of the tag (`VTT`), and decryption-verification
//! (`DVPT`), for 128-, 192- and 256-bit keys.

#![cfg(target_arch = "x86_64")]

use std::collections::HashMap;

use verified_garbage::aes_ccm::{AesCcm, Error};

use super::unhex;

/// The parameters of a file, each from its header or a section header
/// (`[Alen = 0, Plen = 0, ...]`), or the record's own, whichever came last.
type Params<'a> = HashMap<&'a str, &'a str>;

/// Each record of a CCM file (from a `Count` line to the next blank line),
/// with the parameters in force for it.
fn records(text: &str) -> Vec<Params<'_>> {
    let mut params = Params::new();
    let mut out = Vec::new();
    let mut current: Option<Params> = None;
    for line in text.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            if let Some(r) = current.take() {
                out.push(r);
            }
            continue;
        }
        if let Some(header) = line.strip_prefix('[').and_then(|l| l.strip_suffix(']')) {
            for kv in header.split(", ") {
                let (k, v) = kv.split_once(" = ").unwrap();
                params.insert(k, v);
            }
            continue;
        }
        let (k, v) = line.split_once(" = ").unwrap();
        if k == "Count" {
            current = Some(params.clone());
        }
        match current.as_mut() {
            Some(r) => {
                r.insert(k, v);
            }
            None => {
                params.insert(k, v);
            }
        }
    }
    out.extend(current);
    out
}

/// The first `len` bytes of the hex field `k` (CAVP writes `00` for an
/// empty one).
fn bytes(r: &Params, k: &str, len: &str) -> Vec<u8> {
    let n: usize = r[len].parse().unwrap();
    let mut b = unhex(r[k]);
    b.truncate(n);
    assert_eq!(b.len(), n);
    b
}

/// Encrypts `pt` with a `T`-byte tag and decrypts the result.
fn seal<const T: usize>(key: &AesCcm, nonce: &[u8], aad: &[u8], pt: &[u8]) -> Vec<u8> {
    let mut buf = pt.to_vec();
    let tag = key.encrypt_in_place::<T>(nonce, aad, &mut buf).unwrap();
    let ct = [&buf[..], &tag[..]].concat();
    key.decrypt_in_place(nonce, aad, &mut buf, &tag).unwrap();
    assert_eq!(buf, pt);
    ct
}

/// Decrypts `ct` (the encrypted payload followed by a `T`-byte tag).
fn open<const T: usize>(
    key: &AesCcm,
    nonce: &[u8],
    aad: &[u8],
    ct: &[u8],
) -> Result<Vec<u8>, Error> {
    let (data, tag) = ct.split_at(ct.len() - T);
    let mut buf = data.to_vec();
    key.decrypt_in_place::<T>(nonce, aad, &mut buf, tag.try_into().unwrap())?;
    Ok(buf)
}

/// Each tag length Appendix A.1 allows is a separate instance.
macro_rules! by_tag_len {
    ($t:expr, $f:ident($($a:expr),*)) => {
        match $t {
            4 => $f::<4>($($a),*),
            6 => $f::<6>($($a),*),
            8 => $f::<8>($($a),*),
            10 => $f::<10>($($a),*),
            12 => $f::<12>($($a),*),
            14 => $f::<14>($($a),*),
            16 => $f::<16>($($a),*),
            t => panic!("tag length {t}"),
        }
    };
}

#[test]
fn aes_ccm() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("vectors/nist-cavp/ccm");
    let (mut encrypted, mut passed, mut failed) = (0, 0, 0);
    for bits in [128, 192, 256] {
        for kind in ["VADT", "VNT", "VPT", "VTT"] {
            let text = std::fs::read_to_string(dir.join(format!("{kind}{bits}.rsp"))).unwrap();
            for r in records(&text) {
                let key = AesCcm::new(&unhex(r["Key"])).unwrap();
                let nonce = bytes(&r, "Nonce", "Nlen");
                let aad = bytes(&r, "Adata", "Alen");
                let pt = bytes(&r, "Payload", "Plen");
                let t: usize = r["Tlen"].parse().unwrap();
                let ct = by_tag_len!(t, seal(&key, &nonce, &aad, &pt));
                assert_eq!(ct, unhex(r["CT"]), "{kind}{bits} Count {}", r["Count"]);
                encrypted += 1;
            }
        }
        let text = std::fs::read_to_string(dir.join(format!("DVPT{bits}.rsp"))).unwrap();
        for r in records(&text) {
            let key = AesCcm::new(&unhex(r["Key"])).unwrap();
            let nonce = bytes(&r, "Nonce", "Nlen");
            let aad = bytes(&r, "Adata", "Alen");
            let t: usize = r["Tlen"].parse().unwrap();
            let ct = unhex(r["CT"]);
            let got = by_tag_len!(t, open(&key, &nonce, &aad, &ct));
            let at = format!("DVPT{bits} Count {}", r["Count"]);
            match r["Result"] {
                "Pass" => {
                    assert_eq!(got, Ok(bytes(&r, "Payload", "Plen")), "{at}");
                    passed += 1;
                }
                _ => {
                    assert_eq!(got, Err(Error::TagMismatch), "{at}");
                    failed += 1;
                }
            }
        }
    }
    assert!(encrypted > 0 && passed > 0 && failed > 0);
}
