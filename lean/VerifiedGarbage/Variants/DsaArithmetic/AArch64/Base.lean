module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec

/-! # DSA with the shared AArch64 Montgomery arithmetic backend

RSA's Montgomery multiplication with eight-limb products
(`Mont.productEight`, as RSA's CRT window and `vg_rsa_mont_mul` use):
products of distinct operands use the scheduled eight-limb kernel when the
width is a multiple of eight words (every DSA p), and in-place squares RSA's
scheduled squaring kernel. -/

@[expose] public section

namespace VG.Variants.DsaArithmetic.AArch64.Base
open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend where
  mul := Mont.productEight.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.productEight
  verifyVerified := verifying_verified Mont.productEight
  signSp := by decide +kernel
  signDepth := by decide +kernel
  stackBound := by decide
  verifySp := by decide +kernel

end VG.Variants.DsaArithmetic.AArch64.Base
