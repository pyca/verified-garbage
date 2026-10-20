module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Adx

/-! # Precomputed RSA public operation: Adx -/

@[expose] public section

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl := Proof.Variants.RsaPublicPrecomputed.X86_64.Adx.variant

end VG.Variants.RsaPublicPrecomputed.X86_64.Adx
