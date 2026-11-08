module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64.Base
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! # The implementations of `DsaArithmetic` on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.AArch64

open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64 in
def base : Backend := Proof.Variants.DsaArithmetic.AArch64.Base.variant

/-- Every implementation, which each function generic over them is emitted
with (the registration files that import this). -/
def variants := [base]

end VG.Proof.Variants.DsaArithmetic.AArch64
