module

public import VerifiedGarbage.Proof.Aes.X86_64.BlocksVariant
public import VerifiedGarbage.Proof.Aes.X86_64.BlocksResidue

/-! # The implementations of `AesBlocks` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.X86_64

open VG.Proof.Aes.X86_64

/-- AES-NI, with the residue analyses of the functions over it. -/
def aesNi : BlocksImpl :=
  { BlocksImpl.aesni with
    cfb8EncRes := some BlocksResidue.encAesni
    cfb8DecRes := some BlocksResidue.decAesni
    ecbEncRes := some BlocksResidue.ecbAesni }

def scalar : BlocksImpl := .scalar

/-- VAES, with the residue analyses of the functions over it. -/
def vaes : BlocksImpl :=
  { BlocksImpl.vaes with
    cfb8EncRes := some BlocksResidue.encVaes
    cfb8DecRes := some BlocksResidue.decVaes
    ecbEncRes := some BlocksResidue.ecbVaes }

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vaes, aesNi, scalar]

end VG.Proof.Variants.AesBlocks.X86_64
