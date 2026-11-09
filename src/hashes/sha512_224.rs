//! SHA-512/224 (FIPS 180-4).

#![cfg(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    target_arch = "arm",
    target_arch = "x86",
    all(target_arch = "powerpc64", target_endian = "little"),
    target_arch = "riscv64"
))]

use crate::arch::dispatch::sha512::{
    vg_sha512_224_digest_auto, vg_sha512_224_finalize_auto, vg_sha512_224_init_auto,
    vg_sha512_update_auto,
};

super::streaming_hash!(
    /// An incremental SHA-512/224 computation (FIPS 180-4 §6.6).
    Sha512_224 {
        state: 192,
        block: 128,
        output: 28,
        init: vg_sha512_224_init_auto,
        update: vg_sha512_update_auto,
        finalize: vg_sha512_224_finalize_auto,
        digest: vg_sha512_224_digest_auto,
    }
);

#[cfg(test)]
mod tests {
    use super::Sha512_224;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 400] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sha512_224::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sha512_224::default();
                h.update(&msg[..split]);
                let copy = h.clone();
                h.update(&msg[split..len]);
                assert_eq!(h.finalize(), expected);
                let mut h = copy;
                for byte in &msg[split..len] {
                    h.update(core::slice::from_ref(byte));
                }
                assert_eq!(h.finalize(), expected);
            }
        }
    }

    /// The `HashFunction` implementation is the inherent functions.
    #[test]
    fn hash_function() {
        use crate::hashes::HashFunction;
        let msg = [0x5a; 300];
        let mut h = <Sha512_224 as HashFunction>::new();
        HashFunction::update(&mut h, &msg[..100]);
        HashFunction::update(&mut h, &msg[100..]);
        assert_eq!(HashFunction::finalize(h), Sha512_224::digest(&msg));
        assert_eq!(
            <Sha512_224 as HashFunction>::digest(&msg),
            Sha512_224::digest(&msg)
        );
        assert_eq!(
            (
                <Sha512_224 as HashFunction>::OUTPUT_SIZE,
                <Sha512_224 as HashFunction>::BLOCK_SIZE
            ),
            (28, 128)
        );
    }
}
