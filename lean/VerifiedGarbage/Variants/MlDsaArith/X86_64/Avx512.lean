module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2

/-! # ML-DSA's polynomial arithmetic on x86-64: AVX-512 -/

@[expose] public section

namespace VG.Variants.MlDsaArith.X86_64.Avx512

def variant : Proof.MlDsa.X86_64.ArithImpl := .avx512

end VG.Variants.MlDsaArith.X86_64.Avx512
