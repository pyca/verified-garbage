module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee

/-!
# The functions AES-GCM calls on AArch64: AesSha3

A variant of `AesGcm` on AArch64 (see `TCB/Emit.lean`): the AES instructions
for the cipher (`vg_aes_ctr32_aes`, `vg_aes_expand_key_scratch_aes`) and PMULL
and EOR3 for the hash (`vg_ghash_aes_sha3`), which need `FEAT_AES`,
`FEAT_PMULL` (both Rust's `aes` feature) and `FEAT_SHA3`.
-/

@[expose] public section

namespace VG.Variants.AesGcm.AArch64.AesSha3

def variant : Proof.AesGcm.AArch64.GcmVariant := ⟨.aese, .aese, .aesSha3⟩

end VG.Variants.AesGcm.AArch64.AesSha3
