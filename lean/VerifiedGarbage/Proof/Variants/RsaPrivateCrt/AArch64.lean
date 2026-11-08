module

public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64.Base

/-! # The implementations of `RsaPrivateCrt` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.AArch64

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 in
def base : Proof.Rsa.AArch64.CrtImpl := Proof.Variants.RsaPrivateCrt.AArch64.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.RsaPrivateCrt.AArch64
