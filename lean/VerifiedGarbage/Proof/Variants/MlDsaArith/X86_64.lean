module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/-! # The implementations of `MlDsaArith` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.MlDsaArith.X86_64

def avx2 : Proof.MlDsa.X86_64.ArithImpl := .avx2

def avx512 : Proof.MlDsa.X86_64.ArithImpl := .avx512

def sse2 : Proof.MlDsa.X86_64.ArithImpl := .sse2

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [avx2, avx512, sse2]

end VG.Proof.Variants.MlDsaArith.X86_64
