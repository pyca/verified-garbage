module

public import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
public import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedBackend
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcVerified
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.VerifiedPc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
public import VerifiedGarbage.Proof.Rsa.X86_64.CvVerified
import VerifiedGarbage.Proof.Rsa.X86_64.RpVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyVerified
public import VerifiedGarbage.Proof.Rsa.X86_64.PreVerified
import VerifiedGarbage.Proof.Bignum.X86_64.PcFn
import VerifiedGarbage.Proof.Rsa.X86_64.Calls
public import VerifiedGarbage.Proof.Rsa.X86_64.IfmaLit
import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSqFn
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop

/-!
# RSA on x86-64: the proofs `Artifacts/Rsa/X86_64.lean` registers

Each function's `Verified`, made from the proofs of its code and the checks
the kernel evaluates on it (that it inlines, and that every load of MXCSR
restores it).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Instances

open VG.X86_64 VG.Proof.Rsa.X86_64

theorem precompute_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnBase (Proof.Bignum.X86_64.R2Impl.words _)
    (by decide +kernel) rfl (by decide +kernel)

theorem precomputeAdx_verified :
    Verified target (Impl.Rsa.X86_64.Precompute.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Bignum.X86_64.R2Adx.choice Proof.Rsa.X86_64.CallMont.adx.mm))
      (Spec.Rsa.publicPrecomputeContract abi 8) :=
  pc_call_verified Proof.Bignum.X86_64.Mont.fnAdx (Proof.Bignum.X86_64.R2Impl.adx _)
    (by decide +kernel) rfl (by decide +kernel)

theorem crt_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.base.mm
      (Impl.Rsa.X86_64.Crt.expLoopS Proof.Rsa.X86_64.CallMont.lazyBase Proof.Rsa.X86_64.CallMont.base.mm
        Impl.Rsa.X86_64.Crt.tabSelect))
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtCode_correct Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtCode_constantTime Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (Proof.Bignum.X86_64.CrtExpL.w4S_ct Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy))

theorem crtAdx_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Rsa.X86_64.Crt.expLoop5S Proof.Rsa.X86_64.CallMont.lazyAdx Proof.Rsa.X86_64.CallMont.adx.mm
        Impl.Rsa.X86_64.Crt.tabSelectV))
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtCode_correct Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtCode_constantTime Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (Proof.Bignum.X86_64.CrtExpL.w5S_ct Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx))

theorem crtIfma_verified :
    Verified target (Impl.Rsa.X86_64.CrtIfma.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.privateCrtContract abi 8) :=
  crt_call_verified (by lit_decide)
    (Proof.Bignum.X86_64.Ifma.code_correct Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel))
    (Proof.Bignum.X86_64.Ifma.code_constantTime Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel))

theorem crtPre_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.base.mm
      (Impl.Rsa.X86_64.Crt.expLoopS Proof.Rsa.X86_64.CallMont.lazyBase Proof.Rsa.X86_64.CallMont.base.mm
        Impl.Rsa.X86_64.Crt.tabSelect) true)
      (Spec.Rsa.privateCrtPrecomputedContract abi 8) :=
  crtPc_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtPcCode_correct Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtPcCode_constantTime Proof.Bignum.X86_64.Mont.fnBase
      (Proof.Bignum.X86_64.CrtExpL.w4S Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy)
      (Proof.Bignum.X86_64.CrtExpL.w4S_ct Proof.Bignum.X86_64.Mont.fnBase Proof.Bignum.X86_64.MontS.fnLazy))

theorem crtPreAdx_verified :
    Verified target (Impl.Rsa.X86_64.Crt.code Proof.Rsa.X86_64.CallMont.adx.mm
      (Impl.Rsa.X86_64.Crt.expLoop5S Proof.Rsa.X86_64.CallMont.lazyAdx Proof.Rsa.X86_64.CallMont.adx.mm
        Impl.Rsa.X86_64.Crt.tabSelectV) true)
      (Spec.Rsa.privateCrtPrecomputedContract abi 8) :=
  crtPc_call_verified (by decide +kernel)
    (Proof.Bignum.X86_64.crtPcCode_correct Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (by decide +kernel))
    (Proof.Bignum.X86_64.crtPcCode_constantTime Proof.Bignum.X86_64.Mont.fnAdx
      (Proof.Bignum.X86_64.CrtExpL.w5S Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx)
      (Proof.Bignum.X86_64.CrtExpL.w5S_ct Proof.Bignum.X86_64.Mont.fnAdx Proof.Bignum.X86_64.MontS.fnLazyAdx))

theorem crtPreIfma_verified :
    Verified target (Impl.Rsa.X86_64.CrtIfma.code Proof.Rsa.X86_64.CallMont.adx.mm true)
      (Spec.Rsa.privateCrtPrecomputedContract abi 8) :=
  crtPc_call_verified (by lit_decide)
    (Proof.Bignum.X86_64.Ifma.codePc_correct Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (Proof.Bignum.X86_64.Ifma.codePc_constantTime Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel))

theorem crtValues_verified :
    Verified target (Impl.Rsa.X86_64.Keys.CrtValues.code)
      (Spec.Rsa.crtValuesContract abi) :=
  cv_verified (by decide +kernel)

theorem recover_verified :
    Verified target (Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.recoverPrimesContract abi 8) :=
  rp_call_verified Proof.Bignum.X86_64.Mont.fnBase (by decide +kernel) rfl (by decide +kernel)

theorem recoverAdx_verified :
    Verified target (Impl.Rsa.X86_64.Keys.Recover.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.recoverPrimesContract abi 8) :=
  rp_call_verified Proof.Bignum.X86_64.Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)

theorem checkKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckKey.code)
      (Spec.Rsa.checkKeyContract abi) :=
  Key.key_verified (by decide +kernel)

theorem checkCrtKey_verified :
    Verified target (Impl.Rsa.X86_64.CheckCrtKey.code)
      (Spec.Rsa.checkCrtKeyContract abi) :=
  Key.ck_verified (by decide +kernel)

theorem privatePrecompute_verified :
    Verified target Impl.Rsa.X86_64.PrivPre.code (Spec.Rsa.privatePrecomputeContract abi) :=
  Key.pp_verified (by decide +kernel)

end VG.Proof.Rsa.X86_64.Instances
