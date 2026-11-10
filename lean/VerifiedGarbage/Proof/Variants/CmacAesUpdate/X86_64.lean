module

public import VerifiedGarbage.Proof.CmacAes.X86_64.Variant
public import VerifiedGarbage.Proof.Aes.X86_64.Ctr32Residue

/-! # The implementations of `CmacAesUpdate` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.CmacAesUpdate.X86_64

/-- The chaining in AES-NI registers, with the residue analysis of
`vg_cmac_aes_absorb` over it. -/
def aesNi : Proof.CmacAes.X86_64.UpdateImpl :=
  { Proof.CmacAes.X86_64.UpdateImpl.aesniCbc with absorbRes := some Proof.Aes.X86_64.Ctr32Residue.absorbAesni }

def scalar : Proof.CmacAes.X86_64.UpdateImpl := .ctr32 .scalar

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [aesNi, scalar]

end VG.Proof.Variants.CmacAesUpdate.X86_64
