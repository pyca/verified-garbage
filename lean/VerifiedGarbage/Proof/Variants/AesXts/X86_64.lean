module

public import VerifiedGarbage.Proof.AesXts.X86_64.Variant

/-! # The implementations of `AesXts` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesXts.X86_64

def aesNi : Proof.AesXts.X86_64.XtsImpl := .blocks .aesni

def aesNiPclmul : Proof.AesXts.X86_64.XtsImpl := .aesniPclmul

def scalar : Proof.AesXts.X86_64.XtsImpl := .blocks .scalar

def vaes : Proof.AesXts.X86_64.XtsImpl := .blocks .vaes

def vaesVpclmul : Proof.AesXts.X86_64.XtsImpl := .vaesVpclmul

def vaesVpclmulAvx512 : Proof.AesXts.X86_64.XtsImpl := .vaesVpclmulAvx512

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aesNi, aesNiPclmul, scalar, vaes, vaesVpclmul, vaesVpclmulAvx512]

end VG.Proof.Variants.AesXts.X86_64
