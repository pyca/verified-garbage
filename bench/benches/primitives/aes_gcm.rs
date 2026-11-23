//! AES-GCM.

use criterion::Criterion;

pub const USES: &[&str] = &["aes_gcm", "aes", "gcm"];

/// One-shot AES-GCM encryption (in place, and out of place from one piece
/// and from two: a TLS 1.3 record's payload and its content type byte) and
/// decryption (in place and out of place; setup included), and streaming
/// encryption, with a 16-byte
/// key, a 12-byte nonce and 16 bytes of additional data. aws-lc-rs, which
/// has no streaming AES-GCM, is measured one-shot only, with a separate tag
/// as this library's is. The one-shot functions are also measured at `RECORD_SIZES`, the short
/// messages of protocols such as TLS and QUIC, where the fixed costs of a
/// call (the key's setup, the tag) weigh the most, and at `LARGE_SIZES`,
/// whose input and output do not fit in the caches. Encryption with a key
/// used for many messages, as a TLS or QUIC connection's is, is also
/// measured at `REUSED_SIZES`, which are not multiples of 16 blocks (also
/// out of place from two halves, whose second holds whole blocks).
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub fn bench(c: &mut Criterion) {
    use criterion::BenchmarkId;
    use rustls::crypto::cipher::{AeadKey, EncodableVersion, Iv, OutboundPlain, Record, RecordEncrypter};
    use rustls::enums::{ContentType, ProtocolVersion};
    use rustls_verified_garbage::cipher_suite as cs;
    use crate::{BenchDyn, VG};
    use std::hint::black_box;
    for keylen in [16, 24, 32] {
        let key = verified_garbage::aead::aes_gcm::AesGcm::new(&vec![11;keylen]).unwrap();
        let data: Vec<u8> = (0..4099).map(|i| (i*13) as u8).collect();
        for nlen in [8,12,19] {
            let nonce = vec![7;nlen];
            for len in [0,1,15,16,17,31,32,97,4099] {
                let mut expected = data[..len].to_vec();
                let tag = key.encrypt_in_place(&nonce,b"aad",&mut expected).unwrap();
                for split in 0..=len.min(33) {
                    let mid = (split+1).min(len);
                    let parts = [&data[..split], &[], &data[split..mid], &data[mid..len]];
                    let mut out = vec![0xee;len];
                    assert_eq!(key.encrypt(&nonce,b"aad",&parts,&mut out).unwrap(),tag);
                    assert_eq!(out,expected);
                }
            }
        }
    }
    for tls in [12,13] {
        for bits in [128,256] {
            let mut group = c.benchmark_group(format!("record-cutoff-{tls}-{bits}"));
            for size in [64,256,512,1024,2048,3072,4095,4096,4097,6144,8192,10000,16384] {
                let key = if bits == 128 { AeadKey::from([3;16]) } else { AeadKey::from([3;32]) };
                let mut enc:Box<dyn RecordEncrypter> = if tls == 13 {
                    let suite = if bits==128 {cs::TLS13_AES_128_GCM_SHA256} else {cs::TLS13_AES_256_GCM_SHA384};
                    suite.aead_alg.encrypter(key,Iv::new(&[0x55;12]).unwrap())
                } else {
                    let suite = if bits==128 {cs::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256} else {cs::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384};
                    let a=suite.aead_alg;let shape=a.key_block_shape();
                    a.encrypter(key,&vec![0x55;shape.fixed_iv_len],&vec![0x66;shape.explicit_nonce_len])
                };
                let data=vec![0x33;size]; let mut out=Vec::with_capacity(size+64); let mut seq=0;
                group.bench(BenchmarkId::new(VG,size), |b| b.iter(|| {
                    out.clear();
                    let msg=Record::new(ContentType::ApplicationData,EncodableVersion::Legacy(ProtocolVersion::TLSv1_2),OutboundPlain::from(black_box(&data[..])));
                    enc.encrypt(msg,seq,&mut out).unwrap();seq+=1;black_box(&out);
                }));
            }
            group.finish();
        }
    }
}
#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
)))]
pub fn bench(_: &mut Criterion) {}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub(crate) struct Offsets {
    pub(crate) input: usize,
    pub(crate) output: usize,
    pub(crate) aad: usize,
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl Offsets {
    /// The rows' offsets: where rustls puts a record's payload, 5 bytes (the
    /// TLS record header) past the start of an allocation (`PrefixedPayload`,
    /// sealed in place; and the first record in the receive buffer,
    /// `DeframerIter`, opened in place), and the output half a page from the
    /// input, so that sealing out of place never loads and stores at the same
    /// address modulo 4 KiB.
    pub(crate) const DEFAULT: Offsets = Offsets {
        input: 5,
        output: 2048 + 5,
        aad: 0,
    };
}

/// A copy of some bytes at a given offset past a 4 KiB boundary.
#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
pub(crate) struct Aligned {
    raw: Vec<u8>,
    start: usize,
    len: usize,
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl Aligned {
    pub(crate) fn new(bytes: &[u8], offset: usize) -> Self {
        let raw = vec![0u8; bytes.len() + offset + 4096];
        let start = raw.as_ptr().align_offset(4096) + offset;
        let mut a = Aligned {
            raw,
            start,
            len: bytes.len(),
        };
        a.copy_from_slice(bytes);
        a
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl std::ops::Deref for Aligned {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.raw[self.start..self.start + self.len]
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl std::ops::DerefMut for Aligned {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.raw[self.start..self.start + self.len]
    }
}

#[cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]
impl AsRef<[u8]> for Aligned {
    fn as_ref(&self) -> &[u8] {
        self
    }
}

