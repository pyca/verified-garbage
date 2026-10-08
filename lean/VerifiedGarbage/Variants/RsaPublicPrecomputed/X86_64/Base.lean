import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
import VerifiedGarbage.Proof.Rsa.X86_64.Calls

/-! # Precomputed RSA public operation: Base -/

namespace VG.Variants.RsaPublicPrecomputed.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : PublicImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name ++ ""
  code := Impl.Rsa.X86_64.Checked.precomputedChecked CallMont.base.mm
  ok := pd_call_ok (by decide +kernel) (precomputedChecked_correct Mont.fnBase (by decide +kernel))
  ct := pd_call_ct (by decide +kernel) (precomputedChecked_correct Mont.fnBase (by decide +kernel))
    (precomputedChecked_constantTime Mont.fnBase)
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mxSafe := by decide +kernel
  suffix := ""
  features := []

end VG.Variants.RsaPublicPrecomputed.X86_64.Base
