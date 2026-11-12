module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
public import VerifiedGarbage.Proof.AesXts.X86_64.Residue

/-! # The implementations of `AesXts` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.X86_64

def aesNi : Proof.AesXts.X86_64.XtsImpl := .blocks .aesni

/-- AES-NI and PCLMULQDQ, with the residue analyses of the data-unit functions over it. -/
def aesNiPclmul : Proof.AesXts.X86_64.XtsImpl :=
  { Proof.AesXts.X86_64.XtsImpl.aesniPclmul with
    encUnitRes := some Proof.AesXts.X86_64.Residue.encUnitAesniPclmul
    decUnitRes := some Proof.AesXts.X86_64.Residue.decUnitAesniPclmul
    encUnitToRes := some Proof.AesXts.X86_64.Residue.encUnitToAesniPclmul
    decUnitToRes := some Proof.AesXts.X86_64.Residue.decUnitToAesniPclmul }

def scalar : Proof.AesXts.X86_64.XtsImpl := .blocks .scalar

def vaes : Proof.AesXts.X86_64.XtsImpl := .blocks .vaes

/-- VAES and VPCLMULQDQ, with the residue analyses of the data-unit functions over it. -/
def vaesVpclmul : Proof.AesXts.X86_64.XtsImpl :=
  { Proof.AesXts.X86_64.XtsImpl.vaesVpclmul with
    encUnitRes := some Proof.AesXts.X86_64.Residue.encUnitVaesVpclmul
    decUnitRes := some Proof.AesXts.X86_64.Residue.decUnitVaesVpclmul
    encUnitToRes := some Proof.AesXts.X86_64.Residue.encUnitToVaesVpclmul
    decUnitToRes := some Proof.AesXts.X86_64.Residue.decUnitToVaesVpclmul }

/-- AVX-512 VAES, with the residue analyses of the data-unit functions over it. -/
def vaesVpclmulAvx512 : Proof.AesXts.X86_64.XtsImpl :=
  { Proof.AesXts.X86_64.XtsImpl.vaesVpclmulAvx512 with
    encUnitRes := some Proof.AesXts.X86_64.Residue.encUnitVaesVpclmulAvx512
    decUnitRes := some Proof.AesXts.X86_64.Residue.decUnitVaesVpclmulAvx512
    encUnitToRes := some Proof.AesXts.X86_64.Residue.encUnitToVaesVpclmulAvx512
    decUnitToRes := some Proof.AesXts.X86_64.Residue.decUnitToVaesVpclmulAvx512 }

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vaesVpclmulAvx512, vaesVpclmul, aesNiPclmul, vaes, aesNi, scalar]

end VG.Proof.Variants.AesXts.X86_64
