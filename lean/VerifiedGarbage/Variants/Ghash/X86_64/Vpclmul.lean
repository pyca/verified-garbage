module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The implementation of `vg_ghash` on x86-64: Vpclmul

A variant of `Ghash` on x86-64 (see `TCB/Emit.lean`): VPCLMULQDQ on 256-bit registers: `vg_ghash_vpclmul`.
-/

@[expose] public section

namespace VG.Variants.Ghash.X86_64.Vpclmul

def variant : Proof.AesGcm.X86_64.GhashName := .vpclmul

end VG.Variants.Ghash.X86_64.Vpclmul
