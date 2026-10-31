module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-! # The implementation of `vg_ghash` on x86: Scalar -/

@[expose] public section

namespace VG.Variants.Ghash.X86.Scalar

def variant : Proof.AesGcm.X86.GhashName := .scalar

end VG.Variants.Ghash.X86.Scalar
