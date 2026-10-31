module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-! # The implementation of `vg_ghash` on x86-64: Vpclmul -/

@[expose] public section

namespace VG.Variants.Ghash.X86_64.Vpclmul

def variant : Proof.AesGcm.X86_64.GhashName := .vpclmul

end VG.Variants.Ghash.X86_64.Vpclmul
