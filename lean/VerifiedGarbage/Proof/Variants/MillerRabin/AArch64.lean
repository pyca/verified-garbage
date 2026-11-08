module

public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64.Base

/-! # The implementations of `MillerRabin` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.MillerRabin.AArch64

open VG.Proof.MillerRabin.AArch64 VG.Proof.Bignum.AArch64 in
def base : RoundImpl := Proof.Variants.MillerRabin.AArch64.Base.variant

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.MillerRabin.AArch64
