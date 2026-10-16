module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMont
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified

/-!
# DSA with the shared AArch64 Montgomery arithmetic backend: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.AArch64.Base.variant`
(`Variants/DsaArithmetic/AArch64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.AArch64.Base

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

end VG.Proof.Variants.DsaArithmetic.AArch64.Base
