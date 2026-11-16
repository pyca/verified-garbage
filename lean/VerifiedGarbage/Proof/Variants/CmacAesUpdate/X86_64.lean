module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateKeyed

/-! # The implementations of `CmacAesUpdate` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.CmacAesUpdate.X86_64

def aesNi : Proof.CmacAes.X86_64.UpdateImpl := .aesniCbc

/-- Over the bitsliced AES, its round keys bitsliced once for all the blocks
(`Proof/CmacAes/X86_64/UpdateKeyed.lean`). -/
def scalar : Proof.CmacAes.X86_64.UpdateImpl := .keyed

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, scalar]

end VG.Proof.Variants.CmacAesUpdate.X86_64
