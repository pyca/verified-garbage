module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Variant
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmul
public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512

/-! # The implementations of `AesGcm` on x86-64 -/

@[expose] public section

namespace VG.Proof.Variants.AesGcm.X86_64

def aesNi : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .scalar, none⟩

def aesNiPclmul : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .pclmul, none⟩

open VG VG.X86_64 in
def aesNiPclmulAvx : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant

def aesNiVpclmul : Proof.AesGcm.X86_64.GcmVariant := ⟨.aesni, .aesni, .vpclmul, none⟩

def pclmul : Proof.AesGcm.X86_64.GcmVariant := ⟨.scalar, .scalar, .pclmul, none⟩

def scalar : Proof.AesGcm.X86_64.GcmVariant := ⟨.scalar, .scalar, .scalar, none⟩

def vaes : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .scalar, none⟩

def vaesPclmul : Proof.AesGcm.X86_64.GcmVariant := ⟨.vaes, .aesni, .pclmul, none⟩

open VG VG.X86_64 in
def vaesVpclmul : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.VaesVpclmul.variant

open VG VG.X86_64 in
def vaesVpclmulAvx512 : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant

def vpclmul : Proof.AesGcm.X86_64.GcmVariant := ⟨.scalar, .scalar, .vpclmul, none⟩

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [aesNi, aesNiPclmul, aesNiPclmulAvx, aesNiVpclmul, pclmul, scalar, vaes, vaesPclmul, vaesVpclmul, vaesVpclmulAvx512, vpclmul]

end VG.Proof.Variants.AesGcm.X86_64
