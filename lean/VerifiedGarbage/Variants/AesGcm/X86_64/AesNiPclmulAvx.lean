module

public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx

/-! # The functions AES-GCM calls on x86-64: AesNiPclmulAvx -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.AesNiPclmulAvx

open VG VG.X86_64

def variant : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.AesNiPclmulAvx.variant

end VG.Variants.AesGcm.X86_64.AesNiPclmulAvx
