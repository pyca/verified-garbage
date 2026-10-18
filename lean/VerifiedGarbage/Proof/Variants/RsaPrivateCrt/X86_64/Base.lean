module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcVerified
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64.Base
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT1

/-!
# `vg_rsa_private_crt` on x86-64: the baseline: the variant's code and proofs

The variant `VG.Variants.RsaPrivateCrt.X86_64.Base.variant`
(`Variants/RsaPrivateCrt/X86_64/Base.lean`), with the proofs its interface
asks for.
-/

@[expose] public section

namespace VG.Proof.Variants.RsaPrivateCrt.X86_64.Base

open VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

def variant : CrtImpl where
  name := Spec.Rsa.privateCrtApi.name
  code := Impl.Rsa.X86_64.Crt.code CallMont.base.mm
    (Impl.Rsa.X86_64.Crt.expLoopS CallMont.lazyBase CallMont.base.mm Impl.Rsa.X86_64.Crt.tabSelect)
  depth := by decide +kernel
  ok := crt_call_ok (by decide +kernel)
    (crtCode_correct Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (by decide +kernel))
  ct := crt_call_ct (by decide +kernel)
    (crtCode_correct Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (by decide +kernel))
    (crtCode_constantTime Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (CrtExpL.w4S_ct Mont.fnBase MontS.fnLazy))
  nosp := noSp_of (by decide +kernel)
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  montSuffix := ""
  pc := Impl.Rsa.X86_64.Precompute.code CallMont.base.mm
  pcOk := pc_call_ok Mont.fnBase (R2Impl.words _) (by decide +kernel) rfl (by decide +kernel)
  pcCt := pc_call_ct Mont.fnBase (R2Impl.words _) (by decide +kernel) rfl (by decide +kernel)
  pcMx := by decide +kernel
  pubOp := VG.Proof.Variants.RsaPublicPrecomputed.X86_64.Base.variant
  pcNosp := noSp_of (by decide +kernel)
  pcDepth := by decide +kernel
  pcSpSafe := Code.all_of_allInstrs (by decide +kernel)
  pcrtName := Spec.Rsa.privateCrtPrecomputedApi.name
  pcrt := Impl.Rsa.X86_64.Crt.code CallMont.base.mm
    (Impl.Rsa.X86_64.Crt.expLoopS CallMont.lazyBase CallMont.base.mm Impl.Rsa.X86_64.Crt.tabSelect) true
  pcrtDepth := by decide +kernel
  pcrtOk := crtPc_call_ok (by decide +kernel)
    (crtPcCode_correct Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (by decide +kernel))
  pcrtCt := crtPc_call_ct (by decide +kernel)
    (crtPcCode_correct Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (by decide +kernel))
    (crtPcCode_constantTime Mont.fnBase (CrtExpL.w4S Mont.fnBase MontS.fnLazy) (CrtExpL.w4S_ct Mont.fnBase MontS.fnLazy))
  pcrtNosp := noSp_of (by decide +kernel)
  pcrtSpSafe := Code.all_of_allInstrs (by decide +kernel)
  suffix := ""
  features := []

end VG.Proof.Variants.RsaPrivateCrt.X86_64.Base
