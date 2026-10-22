module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-!
# The functions SM4-GCM calls on AArch64: Aes

A variant of `Sm4Gcm` on AArch64 (see `TCB/Emit.lean`): PMULL for the hash
(`vg_ghash_aes`), which needs `FEAT_PMULL`, Rust's `aes` feature.
-/

@[expose] public section

namespace VG.Variants.Sm4Gcm.AArch64.Aes

def variant : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.aes⟩

end VG.Variants.Sm4Gcm.AArch64.Aes
