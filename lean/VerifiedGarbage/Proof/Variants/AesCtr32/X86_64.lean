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
    gcmInitRes := some Ctr32Residue.gcmAesni
    cmacFinishRes := some Ctr32Residue.finishAesni }

def scalar : Ctr32Impl := .scalar

/-- VAES, with the residue analyses of the functions over it. -/
def vaes : Ctr32Impl :=
  { Ctr32Impl.vaes with
    gcmInitRes := some Ctr32Residue.gcmVaes
    cmacFinishRes := some Ctr32Residue.finishVaes }

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vaes, aesNi, scalar]

end VG.Proof.Variants.AesCtr32.X86_64
