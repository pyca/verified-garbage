module

public import VerifiedGarbage.Proof.Aes.X86_64.Variant
public import VerifiedGarbage.Proof.Aes.X86_64.Ctr32Residue

/-! # The implementations of `AesCtr32` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.X86_64

open VG.Proof.Aes.X86_64

/-- AES-NI, with the residue analyses of the functions over it. -/
def aesNi : Ctr32Impl :=
  { Ctr32Impl.aesni with
    cmacFinishRes := some Ctr32Residue.finishAesni
    gcmInitRes := some Ctr32Residue.gcmAesni }

/-- The baseline implementation, with the residue analyses of the functions
over it. -/
def scalar : Ctr32Impl := { Ctr32Impl.scalar with cmacFinishRes := some Ctr32Residue.finishScalar }

/-- VAES, with the residue analyses of the functions over it. -/
def vaes : Ctr32Impl :=
  { Ctr32Impl.vaes with
    cmacFinishRes := some Ctr32Residue.finishVaes
    gcmInitRes := some Ctr32Residue.gcmVaes }

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vaes, aesNi, scalar]

end VG.Proof.Variants.AesCtr32.X86_64
