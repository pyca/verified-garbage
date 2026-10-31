module

public import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64.Base
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont

/-! # DSA with the shared AArch64 Montgomery arithmetic backend -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.AArch64.Base

open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend := Proof.Variants.DsaArithmetic.AArch64.Base.variant

end VG.Variants.DsaArithmetic.AArch64.Base
