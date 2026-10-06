import VerifiedGarbage.Proof.Rsa.AArch64.PublicImpl

/-! # Precomputed RSA public operation on AArch64: Base -/

namespace VG.Variants.RsaPublicPrecomputed.AArch64.Base

open VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ ""
  code := Impl.Rsa.AArch64.Checked.precomputedChecked Mont.base.mm
  ok := precomputedChecked_correct _
  ct := precomputedChecked_constantTime _
  keepsV := by decide +kernel
  spSafe := Code.all_of_forall (fun _ => rfl) _
  depth := by decide +kernel
  suffix := ""
  features := []

end VG.Variants.RsaPublicPrecomputed.AArch64.Base
