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

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [vaesVpclmulAvx512, vaesVpclmul, aesNiPclmul, vaes, aesNi, scalar]

end VG.Proof.Variants.AesXts.X86_64
