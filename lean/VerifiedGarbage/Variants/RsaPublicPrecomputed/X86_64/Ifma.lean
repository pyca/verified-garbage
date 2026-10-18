module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma

/-! # Precomputed RSA public operation: Ifma -/

@[expose] public section

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl := Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant

end VG.Variants.RsaPublicPrecomputed.X86_64.Ifma
