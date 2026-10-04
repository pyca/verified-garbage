//! Machine-code checks of the internal AES encryption and decryption of
//! whole blocks (`vg_aes_encrypt_blocks`, `vg_aes_decrypt_blocks`), each
//! implementation the CPU can run, against the NIST CAVP ECB known-answer
//! tests, vendored unmodified under `vectors/nist-cavp/aes/`.
#![cfg(target_arch = "x86_64")]

use crate::arch::aes::{
    VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES, VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
    vg_aes_decrypt_blocks, vg_aes_decrypt_blocks_aesni, vg_aes_encrypt_blocks,
    vg_aes_encrypt_blocks_aesni, vg_aes_expand_key,
};
use crate::cpu::Features;

type Blocks =
    unsafe extern "sysv64" fn(*const [u8; 240], usize, *mut [u8; 16], usize, *mut [u64; 256]);

/// Each implementation, encryption and decryption, with the features it needs.
const IMPLEMENTATIONS: [(Blocks, Blocks, Features); 2] = [
    (
        vg_aes_encrypt_blocks,
        vg_aes_decrypt_blocks,
        Features::of(&[]),
    ),
    (
        vg_aes_encrypt_blocks_aesni,
        vg_aes_decrypt_blocks_aesni,
        Features::all(&[
            VG_AES_ENCRYPT_BLOCKS_AESNI_FEATURES,
            VG_AES_DECRYPT_BLOCKS_AESNI_FEATURES,
        ]),
    ),
];

const FILES: [&str; 12] = [
    include_str!("../vectors/nist-cavp/aes/ECBGFSbox128.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBGFSbox192.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBGFSbox256.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBKeySbox128.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBKeySbox192.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBKeySbox256.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarKey128.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarKey192.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarKey256.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarTxt128.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarTxt192.rsp"),
    include_str!("../vectors/nist-cavp/aes/ECBVarTxt256.rsp"),
];

/// The most vectors in a row with the same key and direction (`ECBVarTxt`'s).
const MAX: usize = 128;

fn hex<const N: usize>(s: &str) -> ([u8; N], usize) {
    let mut out = [0; N];
    for (i, o) in out.iter_mut().enumerate().take(s.len() / 2) {
        *o = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
    }
    (out, s.len() / 2)
}

/// A run of vectors with the same key and direction: the inputs, and what
/// each implementation must turn them into.
struct Run {
    key: ([u8; 32], usize),
    encrypt: bool,
    input: [[u8; 16]; MAX],
    output: [[u8; 16]; MAX],
    n: usize,
}

impl Run {
    /// Transforms the first `m` inputs, in one call, with each
    /// implementation, and checks them and that the block after them is
    /// untouched; for every `m` up to 17 (two groups of eight and one
    /// more), and all of them.
    fn check(&self) {
        let (key, key_len) = self.key;
        let mut schedule = [0; 240];
        let mut scratch = [0; 64];
        // SAFETY: `key` holds `key_len` (16, 24 or 32) bytes, and the
        // buffers are separate and of the sizes of the signature.
        unsafe { vg_aes_expand_key(key.as_ptr(), key_len, &mut schedule, &mut scratch) };
        let rounds = key_len / 4 + 6;
        for (encrypt, decrypt, features) in IMPLEMENTATIONS {
            if !crate::cpu::detected().contains(features) {
                continue;
            }
            let f = if self.encrypt { encrypt } else { decrypt };
            for m in (0..=self.n.min(17)).chain([self.n]) {
                let mut data = [[0xa5; 16]; MAX + 1];
                data[..self.n].copy_from_slice(&self.input[..self.n]);
                let mut scratch = [0; 256];
                // SAFETY: `rounds` is 10, 12 or 14, `data` holds at least
                // `m` blocks, the CPU has the implementation's features, and
                // the buffers are separate.
                unsafe { f(&schedule, rounds, data.as_mut_ptr(), m, &mut scratch) };
                assert_eq!(data[..m], self.output[..m]);
                assert_eq!(data[m..self.n], self.input[m..self.n]);
                assert_eq!(data[self.n], [0xa5; 16]);
            }
        }
    }
}

#[test]
fn cavp_ecb() {
    let mut vectors = 0;
    for file in FILES {
        let mut run: Option<Run> = None;
        let (mut encrypt, mut key, mut pt, mut ct) = (true, None, None, None);
        for line in file.lines().map(str::trim) {
            match line.split_once(" = ") {
                Some(("KEY", v)) => key = Some(hex::<32>(v)),
                Some(("PLAINTEXT", v)) => pt = Some(hex::<16>(v).0),
                Some(("CIPHERTEXT", v)) => ct = Some(hex::<16>(v).0),
                _ => match line {
                    "[ENCRYPT]" => encrypt = true,
                    "[DECRYPT]" => encrypt = false,
                    _ => {}
                },
            }
            let (Some(k), Some(p), Some(c)) = (key, pt, ct) else {
                continue;
            };
            (key, pt, ct) = (None, None, None);
            let (input, output) = if encrypt { (p, c) } else { (c, p) };
            if let Some(r) = &run
                && (r.key != k || r.encrypt != encrypt)
            {
                r.check();
                run = None;
            }
            let r = run.get_or_insert(Run {
                key: k,
                encrypt,
                input: [[0; 16]; MAX],
                output: [[0; 16]; MAX],
                n: 0,
            });
            r.input[r.n] = input;
            r.output[r.n] = output;
            r.n += 1;
            vectors += 1;
        }
        run.unwrap().check();
    }
    // Every vector of the twelve files.
    assert_eq!(vectors, 2078);
}
