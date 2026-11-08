module

public import VerifiedGarbage.Proof.AesGcm.X86.Callee

/-! # The implementations of `Ghash` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.Ghash.X86

def pclmul : Proof.AesGcm.X86.GhashName := .pclmul

def scalar : Proof.AesGcm.X86.GhashName := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [pclmul, scalar]

end VG.Proof.Variants.Ghash.X86
