import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

/-! # Precomputed RSA public operation: Adx -/

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Checked.precomputedChecked Mont.adx.mm
  ok := precomputedChecked_correct _ (by decide +kernel)
  ct := precomputedChecked_constantTime _
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mxSafe := by decide +kernel
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Variants.RsaPublicPrecomputed.X86_64.Adx
