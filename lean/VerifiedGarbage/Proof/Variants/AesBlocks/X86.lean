module

public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86.Ssse3

/-! # The implementations of `AesBlocks` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.X86

def aesNi : Proof.Aes.X86.BlocksImpl := .aesni

def ssse3 : Proof.Aes.X86.BlocksImpl := Ssse3.variant

def scalar : Proof.Aes.X86.BlocksImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, ssse3, scalar]

end VG.Proof.Variants.AesBlocks.X86
