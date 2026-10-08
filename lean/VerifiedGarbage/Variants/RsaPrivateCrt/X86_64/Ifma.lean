import VerifiedGarbage.Variants.RsaPublicPrecomputed.X86_64.Adx
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit

/-!
# `vg_rsa_private_crt` on x86-64: with AVX512_IFMA

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_ifma`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx` (there is no public operation with
AVX512_IFMA), which need AVX512_IFMA, AVX512F, AVX512VL, AVX, BMI2 and ADX;
its Montgomery multiplications outside the vector code are calls of
`vg_rsa_mont_mul_adx`.
-/

namespace VG.Variants.RsaPrivateCrt.X86_64.Ifma

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl where
  name := Spec.Rsa.privateCrtApi.name ++ "_ifma"
  code := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm
  depth := by lit_decide
  ok := crt_call_ok (by lit_decide) (Ifma.code_correct Mont.fnAdx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
  ct := crt_call_ct (by lit_decide) (Ifma.code_correct Mont.fnAdx (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)) (Ifma.code_constantTime Mont.fnAdx (by decide +kernel))
  nosp := noSp_of (by lit_decide)
  spSafe := Code.all_of_allInstrs (by lit_decide)
  montSuffix := "_adx"
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.adx.mm
  pcOk := pc_call_ok Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Variants.RsaPublicPrecomputed.X86_64.Adx.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

end VG.Variants.RsaPrivateCrt.X86_64.Ifma
