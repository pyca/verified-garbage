module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.FoldedChecked
import Mathlib.Tactic.Finiteness.Attr

/-!
# `vg_rsa_private_crt` on AArch64: the baseline: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.AArch64.Base.variant`
(`Variants/RsaPrivateCrt/AArch64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

def variant : Proof.Rsa.AArch64.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := WindowFive.code
  verified := WindowFive.base_verified
  noFrames := by decide +kernel
  pcName := Spec.Rsa.publicPrecomputeApi.name
  pc := Impl.Rsa.AArch64.Precompute.code Mont.base.mm
  pcVerified := precompute_verified Mont.base
  pcNoFrames := by decide +kernel
  pdName := Spec.Rsa.publicPrecomputedCheckedApi.name
  pd := Impl.Rsa.AArch64.Folded.checked Mont.productEight.mm
  pdVerified := Proof.Rsa.AArch64.FoldedPublic.checked_verified Mont.productEight
  pdNoFrames := by decide +kernel
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPrivateCrt.AArch64.Base
