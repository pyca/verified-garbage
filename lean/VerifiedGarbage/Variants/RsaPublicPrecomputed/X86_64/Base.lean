module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Base

/-! # Precomputed RSA public operation: Base -/

@[expose] public section

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl := Proof.Variants.RsaPublicPrecomputed.X86_64.Base.variant

end VG.Variants.RsaPublicPrecomputed.X86_64.Base
