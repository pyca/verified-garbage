module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.BackendAvx2
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/-! # The implementations of `MlDsaArith` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.MlDsaArith.X86_64

def avx2 : Proof.MlDsa.X86_64.ArithImpl := .avx2

def avx512 : Proof.MlDsa.X86_64.ArithImpl := .avx512

def sse2 : Proof.MlDsa.X86_64.ArithImpl := .sse2

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [avx512, avx2, sse2]

/-- The implementations of the arithmetic but the samplers, best first: those
of `variants` but `avx512`, which differs from `avx2` only in its samplers
(`rej4`, `expandMask4`), for the functions that call no sampler (the
preparation of keys; their instances for `avx512` would be `avx2`'s). -/
def samplerFreeVariants := [avx2, sse2]

end VG.Proof.Variants.MlDsaArith.X86_64
