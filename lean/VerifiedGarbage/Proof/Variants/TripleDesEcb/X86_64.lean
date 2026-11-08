module

public import VerifiedGarbage.Proof.TripleDes.X86_64.Batch.Call

/-! # The implementations of `TripleDesEcb` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.TripleDesEcb.X86_64

def avx2 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx2

def avx512 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.avx512

def sse2 : Proof.TripleDes.X86_64.Batch.EcbImpl := Proof.TripleDes.X86_64.Batch.sse

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [avx512, avx2, sse2]

end VG.Proof.Variants.TripleDesEcb.X86_64
