module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-! # The implementation of `vg_ghash` on x86: Pclmul -/

@[expose] public section

namespace VG.Variants.Ghash.X86.Pclmul

def variant : Proof.AesGcm.X86.GhashName := .pclmul

end VG.Variants.Ghash.X86.Pclmul
