//! SM3 (GB/T 32905-2016, as transcribed in draft-sca-cfrg-sm3-02).
//!
//! `vg_sm3_init`, `vg_sm3_update` and `vg_sm3_finalize` (contracts
//! `VG.Spec.Sm3.initContract`, `updateContract` and `finalizeContract`)
//! maintain a streaming state that represents the message absorbed so far
//! (`VG.Spec.Sm3.Repr`: the hash value after its whole blocks, and its
//! remaining bytes), and pad it and output the hash value.

#![cfg(target_arch = "x86_64")]

use crate::arch::sm3::{vg_sm3_finalize, vg_sm3_init, vg_sm3_update};

super::streaming_hash!(
    /// An incremental SM3 computation.
    Sm3 {
        state: 96,
        block: 64,
        output: 32,
        init: vg_sm3_init,
        backends: Sm3Backend {
            Scalar => (vg_sm3_update, vg_sm3_finalize),
        },
    }
);

#[cfg(test)]
mod tests {
    use super::Sm3;

    /// Every way of splitting a message into two updates gives the same
    /// digest, for every length around the padding boundaries.
    #[test]
    fn incremental() {
        let msg: [u8; 200] = core::array::from_fn(|i| (i * 7 + 3) as u8);
        for len in 0..msg.len() {
            let expected = Sm3::digest(&msg[..len]);
            for split in 0..=len {
                let mut h = Sm3::default();
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
}
