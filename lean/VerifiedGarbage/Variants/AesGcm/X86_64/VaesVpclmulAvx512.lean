module

public import VerifiedGarbage.Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512

/-! # The functions AES-GCM calls on x86-64: VaesVpclmulAvx512 -/

@[expose] public section

namespace VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512

open VG VG.X86_64

def variant : Proof.AesGcm.X86_64.GcmVariant := Proof.Variants.AesGcm.X86_64.VaesVpclmulAvx512.variant

end VG.Variants.AesGcm.X86_64.VaesVpclmulAvx512
