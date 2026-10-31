module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-! # The implementation of `vg_ghash` on x86-64: Pclmul -/

@[expose] public section

namespace VG.Variants.Ghash.X86_64.Pclmul

def variant : Proof.AesGcm.X86_64.GhashName := .pclmul

end VG.Variants.Ghash.X86_64.Pclmul
