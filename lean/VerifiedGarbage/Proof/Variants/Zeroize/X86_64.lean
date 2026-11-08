module

public import VerifiedGarbage.Proof.Zeroize.X86_64Impl

/-! # The implementations of `Zeroize` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Zeroize.X86_64

def avx : Proof.Zeroize.X86_64.ZeroizeImpl := .avx

def scalar : Proof.Zeroize.X86_64.ZeroizeImpl := .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [avx, scalar]

end VG.Proof.Variants.Zeroize.X86_64
