import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Rsa.X86_64.Calls

/-! # Precomputed RSA public operation: Adx -/

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Folded.checked CallMont.adx.mm
  ok := pd_call_ok (by decide +kernel) (FoldedPublic.checked_correct Mont.fnAdx (by decide +kernel) (by decide +kernel))
  ct := pd_call_ct (by decide +kernel) (FoldedPublic.checked_correct Mont.fnAdx (by decide +kernel) (by decide +kernel))
    (FoldedPublic.checked_ct Mont.fnAdx fnAdx_final_ct)
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mxSafe := by decide +kernel
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Variants.RsaPublicPrecomputed.X86_64.Adx
