module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # DSA with the shared AArch64 Montgomery arithmetic backend -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.AArch64.Base
open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend where
  mul := Mont.base.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.base
  verifyVerified := verifying_verified Mont.base
  signSp := by decide +kernel
  verifySp := by decide +kernel

end VG.Variants.DsaArithmetic.AArch64.Base
