import VerifiedGarbage.Variants.RsaPublicPrecomputed.X86_64.Adx
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBackend

/-!
# `vg_rsa_private_crt` on x86-64: with AVX512_IFMA

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_ifma`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx` (there is no public operation with
AVX512_IFMA), which need AVX512_IFMA, AVX512F, AVX512VL, AVX, BMI2 and ADX.
-/

namespace VG.Variants.RsaPrivateCrt.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

def variant : Proof.Rsa.X86_64.CrtImpl where
  name := Spec.Rsa.privateCrtApi.name ++ "_ifma"
  code := Impl.Rsa.X86_64.CrtIfma.code Mont.adxSquare.mm
  depth := by decide +kernel
  ok := Ifma.code_correct _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  ct := Ifma.code_constantTime _ (by decide +kernel)
  nosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  mont := Mont.adxSquare
  montSuffix := "_adx"
  pcMx := by decide +kernel
  pubOp := VG.Variants.RsaPublicPrecomputed.X86_64.Adx.variant
  pcNosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

end VG.Variants.RsaPrivateCrt.X86_64.Ifma
