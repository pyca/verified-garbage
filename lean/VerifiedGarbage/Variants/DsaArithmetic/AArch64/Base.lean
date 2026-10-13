module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Baseline AArch64 Montgomery arithmetic for DSA

RSA's default AArch64 Montgomery multiplication (`Mont.base`), whose
in-place squares call RSA's shared scheduled squaring kernel.
-/

@[expose] public section

namespace VG.Variants.DsaArithmetic.AArch64.Base
open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend where
  mul := Mont.base.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.base
  verifyVerified := verifying_verified Mont.base

end VG.Variants.DsaArithmetic.AArch64.Base
