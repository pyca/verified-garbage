module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicPrecomputeKernel
public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
import VerifiedGarbage.Proof.Bignum.Arm.R2Public
import VerifiedGarbage.Proof.Bignum.Arm.R2PublicCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputePublicCT

/-! ### `Bignum.Arm.PublicPrecomputeNormalized`, which only this module used -/

section

/-! Public normalized setup supplies the same kernel interface as the original setup. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def normalizedPublicPrecomputeKernel : PublicPrecomputeKernel where
  code := precomputeWith r2Public
  correct := by exact precomputeWith_ok ⟨r2Public, r2Public_ok⟩
  ct := by exact precomputePublic_ct ⟨r2Public, r2Public_ok⟩ r2Public_ct

end VG.Proof.Bignum.Arm

end

end


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
  crtPName := "vg_rsa_private_crt_precomputed"
  crtP := CrtFn.codeGiven baselineWindowKernel.code
  crtPVerified := crt_verifiedP
  crtPStack := by decide +kernel
  pcName := Spec.Rsa.publicPrecomputeApi.name
  pc := PcFn.codeWith normalizedPublicPrecomputeKernel.code
  pcVerified := precompute_verified (kernel := normalizedPublicPrecomputeKernel)
  pcStack := by decide +kernel
  pdName := "vg_rsa_public_precomputed_checked"
  pd := PdFn.code
  pdVerified := pd_verified
  pdStack := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPrivateCrt.Arm.Base
