module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Callee

/-! # The implementations of `Ghash` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.Ghash.X86_64

def pclmul : Proof.AesGcm.X86_64.GhashName := .pclmul

def scalar : Proof.AesGcm.X86_64.GhashName := .scalar

def vpclmul : Proof.AesGcm.X86_64.GhashName := .vpclmul

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vpclmul, pclmul, scalar]

end VG.Proof.Variants.Ghash.X86_64
