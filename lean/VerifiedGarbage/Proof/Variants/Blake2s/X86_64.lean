module

public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64.Avx
public import VerifiedGarbage.Proof.Variants.Blake2s.X86_64.Scalar

/-! # The implementations of `Blake2s` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Blake2s.X86_64

def avx : Proof.Blake2.X86_64.BackendS := Proof.Variants.Blake2s.X86_64.Avx.variant

def scalar : Proof.Blake2.X86_64.BackendS := Proof.Variants.Blake2s.X86_64.Scalar.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [avx, scalar]

end VG.Proof.Variants.Blake2s.X86_64
