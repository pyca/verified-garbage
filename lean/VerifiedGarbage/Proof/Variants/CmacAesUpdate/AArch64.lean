module

public import VerifiedGarbage.Proof.CmacAes.AArch64.Variant

/-! # The implementations of `CmacAesUpdate` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.CmacAesUpdate.AArch64

def aese : Proof.CmacAes.AArch64.UpdateImpl := .aese

def scalar : Proof.CmacAes.AArch64.UpdateImpl := .ctr32 .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aese, scalar]

end VG.Proof.Variants.CmacAesUpdate.AArch64
