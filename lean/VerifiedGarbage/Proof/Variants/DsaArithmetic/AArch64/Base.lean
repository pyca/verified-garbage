module

public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Bignum.AArch64.MulFixedCallMont
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingVerified

/-!
# DSA with the shared AArch64 Montgomery arithmetic backend: the variant's code and proofs

The variant `VG.Variants.DsaArithmetic.AArch64.Base.variant`
(`Variants/DsaArithmetic/AArch64/Base.lean`), with the proofs its interface
asks for. Its repeated products call their fixed-index helpers
(`vg_rsa_mul_{o}_{a}_{b}`, `Mont.calledProductEight`) rather than each
inlining the eight-limb kernel.
-/

@[expose] public section

namespace VG.Proof.Variants.DsaArithmetic.AArch64.Base

open VG VG.AArch64 VG.Proof.Dsa.AArch64 VG.Proof.Bignum.AArch64

def variant : Backend where
  mul := Mont.calledProductEight.mm
  suffix := ""
  features := []
  signVerified := signing_verified Mont.calledProductEight
  verifyVerified := verifying_verified Mont.calledProductEight
  parametersVerified := parameters_verified Mont.calledProductEight
  deriveVerified := derive_verified Mont.calledProductEight
  parametersSp := by decide +kernel
  parametersDepth := by decide +kernel
  deriveSp := by decide +kernel
  deriveDepth := by decide +kernel
  signSp := by decide +kernel
  signDepth := by decide +kernel
  stackBound := by decide
  verifySp := by decide +kernel

end VG.Proof.Variants.DsaArithmetic.AArch64.Base
