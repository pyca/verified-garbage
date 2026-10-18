module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VerifiedPc
public import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1

/-!
# `vg_rsa_private_crt` on x86-64: with AVX512_IFMA: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.X86_64.Ifma.variant`
(`Variants/RsaPrivateCrt/X86_64/Ifma.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86_64.Ifma

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
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.adx.mm (Impl.Bignum.X86_64.R2Adx.choice CallMont.adx.mm)
  pcOk := pc_call_ok Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Ifma.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  pcrtName := Spec.Rsa.privateCrtPrecomputedApi.name ++ "_ifma"
  pcrt := Impl.Rsa.X86_64.CrtIfma.code CallMont.adx.mm true
  pcrtDepth := by lit_decide
  pcrtOk := crtPc_call_ok (by lit_decide) (Ifma.codePc_correct Mont.fnAdx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel))
  pcrtCt := crtPc_call_ct (by lit_decide) (Ifma.codePc_correct Mont.fnAdx (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)) (Ifma.codePc_constantTime Mont.fnAdx (by decide +kernel))
  pcrtNosp := noSp_of (by lit_decide)
  pcrtSpSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_ifma"
  features := ["avx", "avx512f", "avx512ifma", "avx512vl", "bmi2", "adx"]

end VG.Proof.Variants.RsaPrivateCrt.X86_64.Ifma
