module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-!
# The implementation of `vg_ghash` on x86-64: Scalar

A variant of `Ghash` on x86-64 (see `TCB/Emit.lean`): the baseline ISA: `vg_ghash`.
-/

@[expose] public section

namespace VG.Variants.Ghash.X86_64.Scalar

def variant : Proof.AesGcm.X86_64.GhashName := .scalar

end VG.Variants.Ghash.X86_64.Scalar
