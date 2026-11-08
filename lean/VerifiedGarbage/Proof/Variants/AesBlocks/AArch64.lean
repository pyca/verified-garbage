module

public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant

/-! # The implementations of `AesBlocks` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.AArch64

def aes : Proof.Aes.AArch64.BlocksImpl := .aese

def scalar : Proof.Aes.AArch64.BlocksImpl := .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aes, scalar]

end VG.Proof.Variants.AesBlocks.AArch64
