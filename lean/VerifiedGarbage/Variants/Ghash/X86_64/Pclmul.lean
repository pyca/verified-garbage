module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The implementation of `vg_ghash` on x86-64: Pclmul

A variant of `Ghash` on x86-64 (see `TCB/Emit.lean`): PCLMULQDQ: `vg_ghash_pclmul`.
-/

@[expose] public section

namespace VG.Variants.Ghash.X86_64.Pclmul

def variant : Proof.AesGcm.X86_64.GhashName := .pclmul

end VG.Variants.Ghash.X86_64.Pclmul
