module

public import VerifiedGarbage.Proof.AesXts.AArch64.Variant

/-! # The implementations of `AesXts` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.AArch64

def aes : Proof.AesXts.AArch64.XtsImpl := .aes

def scalar : Proof.AesXts.AArch64.XtsImpl := .blocks .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aes, scalar]

end VG.Proof.Variants.AesXts.AArch64
