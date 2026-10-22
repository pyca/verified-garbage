module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-!
# The implementation of `vg_ghash` on x86: Pclmul

A variant of `Ghash` on x86 (see `TCB/Emit.lean`): PCLMULQDQ: `vg_ghash_pclmul`.
-/

@[expose] public section

namespace VG.Variants.Ghash.X86.Pclmul

def variant : Proof.AesGcm.X86.GhashName := .pclmul

end VG.Variants.Ghash.X86.Pclmul
