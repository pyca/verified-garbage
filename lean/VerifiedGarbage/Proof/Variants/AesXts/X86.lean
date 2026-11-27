module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Verified
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # The implementations of `AesXts` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.X86

def aesNi : Proof.AesXts.X86.XtsImpl := .aesni

def ssse3 : Proof.AesXts.X86.XtsImpl := .blocks AesBlocks.X86.ssse3

def scalar : Proof.AesXts.X86.XtsImpl := .blocks .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, ssse3, scalar]

end VG.Proof.Variants.AesXts.X86
