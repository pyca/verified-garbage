module

public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Adx
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL
import VerifiedGarbage.Proof.Bignum.Amm52
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCode

/-!
# `vg_rsa_private_crt` on x86-64: with BMI2 and ADX: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.X86_64.Adx.variant`
(`Variants/RsaPrivateCrt/X86_64/Adx.lean`), with the proofs its interface asks
for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86_64.Adx

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl where
  name := Spec.Rsa.privateCrtApi.name ++ "_adx"
  code := Impl.Rsa.X86_64.Crt.code CallMont.adx.mm
    (Impl.Rsa.X86_64.Crt.expLoop5S CallMont.lazyAdx CallMont.adx.mm Impl.Rsa.X86_64.Crt.tabSelectV)
  depth := by decide +kernel
  ok := crt_call_ok (by decide +kernel)
    (crtCode_correct Mont.fnAdx (CrtExpL.w5S Mont.fnAdx MontS.fnLazyAdx) (by decide +kernel))
  ct := crt_call_ct (by decide +kernel)
    (crtCode_correct Mont.fnAdx (CrtExpL.w5S Mont.fnAdx MontS.fnLazyAdx) (by decide +kernel))
    (crtCode_constantTime Mont.fnAdx (CrtExpL.w5S Mont.fnAdx MontS.fnLazyAdx)
      (CrtExpL.w5S_ct Mont.fnAdx MontS.fnLazyAdx))
  nosp := noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  montSuffix := "_adx"
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.adx.mm (Impl.Bignum.X86_64.R2Adx.choice CallMont.adx.mm)
  pcOk := pc_call_ok Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnAdx (R2Impl.adx _) (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Adx.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := "_adx"
  features := ["avx", "avx2", "bmi2", "adx"]

end VG.Proof.Variants.RsaPrivateCrt.X86_64.Adx
