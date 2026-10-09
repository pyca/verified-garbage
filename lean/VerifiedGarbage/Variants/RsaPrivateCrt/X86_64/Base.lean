import VerifiedGarbage.Variants.RsaPublicPrecomputed.X86_64.Base
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86_64.Calls

/-!
# `vg_rsa_private_crt` on x86-64: the baseline

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`, all three by calls of `vg_rsa_mont_mul`.
Its callers keep their plain names.
-/

namespace VG.Variants.RsaPrivateCrt.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := Impl.Rsa.X86_64.Crt.code CallMont.base.mm
  depth := by decide +kernel
  ok := crt_call_ok (by decide +kernel) (crtCode_correct Mont.fnBase (by decide +kernel))
  ct := crt_call_ct (by decide +kernel) (crtCode_correct Mont.fnBase (by decide +kernel)) (crtCode_constantTime Mont.fnBase)
  nosp := noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  montSuffix := ""
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.base.mm
  pcOk := pc_call_ok Mont.fnBase (R2Impl.words _) (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnBase (R2Impl.words _) (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Variants.RsaPublicPrecomputed.X86_64.Base.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

end VG.Variants.RsaPrivateCrt.X86_64.Base
