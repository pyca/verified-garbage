import VerifiedGarbage.Proof.Rsa.AArch64.PrivImpl
import VerifiedGarbage.Proof.Bignum.AArch64.CrtVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked

/-!
# `vg_rsa_private_crt` on AArch64: the baseline

A variant of `RsaPrivateCrt` on AArch64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`. Its callers keep their plain names.
-/

namespace VG.Variants.RsaPrivateCrt.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

def variant : Proof.Rsa.AArch64.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := Impl.Rsa.AArch64.Crt.code Mont.base.mm
  verified := crt_verified Mont.base
  noFrames := by decide +kernel
  pcName := Spec.Rsa.publicPrecomputeApi.name
  pc := Impl.Rsa.AArch64.Precompute.code Mont.base.mm
  pcVerified := precompute_verified Mont.base
  pcNoFrames := by decide +kernel
  pdName := Spec.Rsa.publicPrecomputedCheckedApi.name
  pd := Impl.Rsa.AArch64.Checked.precomputedChecked Mont.base.mm
  pdVerified := Proof.Rsa.AArch64.precomputedChecked_verified Mont.base
  pdNoFrames := by decide +kernel
  suffix := ""
  features := []

end VG.Variants.RsaPrivateCrt.AArch64.Base
