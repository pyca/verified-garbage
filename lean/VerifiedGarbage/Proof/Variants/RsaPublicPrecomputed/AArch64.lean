module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64.Base

/-! # The implementations of `RsaPublicPrecomputed` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.RsaPublicPrecomputed.AArch64

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 in
def base : PublicImpl := Proof.Variants.RsaPublicPrecomputed.AArch64.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [base]

end VG.Proof.Variants.RsaPublicPrecomputed.AArch64
