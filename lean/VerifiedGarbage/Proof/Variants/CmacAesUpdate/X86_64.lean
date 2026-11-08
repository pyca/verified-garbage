module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant

/-! # The implementations of `CmacAesUpdate` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.CmacAesUpdate.X86_64

def aesNi : Proof.CmacAes.X86_64.UpdateImpl := .aesniCbc

def scalar : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .scalar

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aesNi, scalar]

end VG.Proof.Variants.CmacAesUpdate.X86_64
