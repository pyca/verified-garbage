module

public import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl

/-! # The implementations of `MlKemSample4` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.MlKemSample4.X86_64

def avx2 : Proof.MlKem.X86_64.Sample4Impl := .avx2

def avx512 : Proof.MlKem.X86_64.Sample4Impl := .avx512

def scalar : Proof.MlKem.X86_64.Sample4Impl := .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [avx2, avx512, scalar]

end VG.Proof.Variants.MlKemSample4.X86_64
