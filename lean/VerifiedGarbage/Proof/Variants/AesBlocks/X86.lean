module

public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant

/-! # The implementations of `AesBlocks` on x86 (32-bit) -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.X86

def aesNi : Proof.Aes.X86.BlocksImpl := .aesni

def scalar : Proof.Aes.X86.BlocksImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, scalar]

end VG.Proof.Variants.AesBlocks.X86
