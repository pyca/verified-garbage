module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64.Neon

/-! # The implementations of `AesXts` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.AArch64

def aes : Proof.AesXts.AArch64.XtsImpl := .aes

def neon : Proof.AesXts.AArch64.XtsImpl := .blocks Proof.Variants.AesBlocks.AArch64.neon

def scalar : Proof.AesXts.AArch64.XtsImpl := .blocks .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aes, neon, scalar]

end VG.Proof.Variants.AesXts.AArch64
