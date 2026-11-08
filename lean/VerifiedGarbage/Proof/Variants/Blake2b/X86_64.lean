module

public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Avx2
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Avx512
public import VerifiedGarbage.Proof.Variants.Blake2b.X86_64.Scalar

/-! # The implementations of `Blake2b` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Blake2b.X86_64

def avx2 : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Avx2.variant

def avx512 : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Avx512.variant

def scalar : Proof.Blake2.X86_64.Backend := Proof.Variants.Blake2b.X86_64.Scalar.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [avx512, avx2, scalar]

end VG.Proof.Variants.Blake2b.X86_64
