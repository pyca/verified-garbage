module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call

/-! # The implementations of `TripleDesEcb` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.TripleDesEcb.X86_64

def avx2 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx2

def avx512 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx512

def sse2 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.sse

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [avx2, avx512, sse2]

end VG.Proof.Variants.TripleDesEcb.X86_64
