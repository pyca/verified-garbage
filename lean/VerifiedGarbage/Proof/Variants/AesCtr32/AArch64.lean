module

public import VerifiedGarbage.Proof.Aes.AArch64.Variant

/-! # The implementations of `AesCtr32` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.AArch64

def aese : Proof.Aes.AArch64.Ctr32Impl := .aese

def scalar : Proof.Aes.AArch64.Ctr32Impl := .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aese, scalar]

end VG.Proof.Variants.AesCtr32.AArch64
