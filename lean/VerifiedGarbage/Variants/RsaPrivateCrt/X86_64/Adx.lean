import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend

/-!
# `vg_rsa_private_crt` on x86-64: with BMI2 and ADX

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_adx`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx`, which need BMI2 and ADX.
-/

namespace VG.Variants.RsaPrivateCrt.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def variant : Proof.Rsa.X86_64.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Crt.code Mont.adxSquare.mm
  depth := by decide +kernel
  ok := crtCode_correct _ (by decide +kernel)
  ct := crtCode_constantTime _
  nosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mont := Mont.adxSquare
  montSuffix := "_adx"
  pcMx := by decide +kernel
  pdMx := by decide +kernel
  pcNosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  pdNosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pdDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  pdSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_adx"
  features := ["bmi2", "adx"]

end VG.Variants.RsaPrivateCrt.X86_64.Adx
