module

public import VerifiedGarbage.Variants.RsaPublicPrecomputed.X86_64.Adx
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain

/-!
# `vg_rsa_private_crt` on x86-64: with BMI2 and ADX

A variant of `RsaPrivateCrt` on x86-64 (see `TCB/Emit.lean`):
`vg_rsa_private_crt_adx`, checked with `vg_rsa_public_precompute_adx` and
`vg_rsa_public_precomputed_checked_adx`, all three by calls of
`vg_rsa_mont_mul_adx`, which needs BMI2 and ADX; the first reads its table
with AVX2 (`Crt.tabSelectV`).
-/

@[expose] public section

namespace VG.Variants.RsaPrivateCrt.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl where
  name := Spec.Rsa.privateCrtApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Crt.code CallMont.adx.mm Impl.Rsa.X86_64.Crt.tabSelectV
  depth := by decide +kernel
  ok := crt_call_ok (by decide +kernel) (crtCode_correct Mont.fnAdx CrtSel.avx (by decide +kernel))
  ct := crt_call_ct (by decide +kernel) (crtCode_correct Mont.fnAdx CrtSel.avx (by decide +kernel)) (crtCode_constantTime Mont.fnAdx CrtSel.avx tabSelV_ct)
  nosp := noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  montSuffix := "_adx"
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.adx.mm (Impl.Bignum.X86_64.R2Adx.choice CallMont.adx.mm)
  pcOk := pc_call_ok Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Variants.RsaPublicPrecomputed.X86_64.Adx.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_adx"
  features := ["avx", "avx2", "bmi2", "adx"]

end VG.Variants.RsaPrivateCrt.X86_64.Adx
