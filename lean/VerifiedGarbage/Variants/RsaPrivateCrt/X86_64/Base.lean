import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified

/-!
# `vg_rsa_private_crt` on x86-64: the baseline

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt`, checked with `vg_rsa_public_precompute` and
`vg_rsa_public_precomputed_checked`. Its callers keep their plain names.
-/

namespace VG.Variants.RsaPrivateCrt.X86_64.Base

open VG.X86_64 VG.Proof.Bignum.X86_64

def variant : Proof.Rsa.X86_64.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := Impl.Rsa.X86_64.Crt.code Mont.base.mm
  depth := by decide +kernel
  ok := crtCode_correct _ (by decide +kernel)
  ct := crtCode_constantTime _
  nosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mont := Mont.base
  montSuffix := ""
  pcMx := by decide +kernel
  pdMx := by decide +kernel
  pcNosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  pdNosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pdDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  pdSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

end VG.Variants.RsaPrivateCrt.X86_64.Base
