module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/-! # ML-DSA's polynomial arithmetic on x86-64: SSE2 -/

@[expose] public section

namespace VG.Variants.MlDsaArith.X86_64.Sse2

def variant : Proof.MlDsa.X86_64.ArithImpl := .sse2

end VG.Variants.MlDsaArith.X86_64.Sse2
