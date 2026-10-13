module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowBase
public import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
public import VerifiedGarbage.Proof.Rsa.AArch64.FoldedChecked

/-!
# `vg_rsa_private_crt` on AArch64: the baseline

A variant of `RsaPrivateCrt` on AArch64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`. Its callers keep their plain names.
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.AArch64.Base

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
  pd := Impl.Rsa.AArch64.Folded.checked Mont.base.mm
  pdVerified := Proof.Rsa.AArch64.FoldedPublic.checked_verified Mont.base
  pdNoFrames := by decide +kernel
  suffix := ""
  features := []

end VG.Variants.RsaPrivateCrt.AArch64.Base
