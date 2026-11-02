module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeNormalized

/-!
# `vg_rsa_private_crt` on ARMv7: the baseline: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.Arm.Base.variant`
(`Variants/RsaPrivateCrt/Arm/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.Arm.Base

open VG.Arm VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm

def variant : Proof.Rsa.Arm.CrtImpl where
  name := "vg_rsa_private_crt"
  code := CrtFn.code
  verified := crt_verified
  stack := by decide +kernel
  pcName := Spec.Rsa.publicPrecomputeApi.name
  pc := PcFn.codeWith normalizedPublicPrecomputeKernel.code
  pcVerified := precompute_verified (kernel := normalizedPublicPrecomputeKernel)
  pcStack := by decide +kernel
  pdName := Spec.Rsa.publicPrecomputedCheckedApi.name
  pd := PdFn.code
  pdVerified := pd_verified
  pdStack := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPrivateCrt.Arm.Base
