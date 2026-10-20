module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64.Base

/-! # Precomputed RSA public operation on AArch64: Base -/

@[expose] public section

namespace VG.Variants.RsaPublicPrecomputed.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

def variant : PublicImpl := Proof.Variants.RsaPublicPrecomputed.AArch64.Base.variant

end VG.Variants.RsaPublicPrecomputed.AArch64.Base
