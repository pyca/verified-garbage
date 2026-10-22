module

public import VerifiedGarbage.Proof.Sm4Gcm.AArch64.Instances

/-!
# The functions SM4-GCM calls on AArch64: Scalar

A variant of `Sm4Gcm` on AArch64 (see `TCB/Emit.lean`): the baseline ISA for
the hash (`vg_ghash`).
-/

@[expose] public section

namespace VG.Variants.Sm4Gcm.AArch64.Scalar

def variant : Proof.Sm4Gcm.AArch64.GcmVariant := ⟨.scalar⟩

end VG.Variants.Sm4Gcm.AArch64.Scalar
