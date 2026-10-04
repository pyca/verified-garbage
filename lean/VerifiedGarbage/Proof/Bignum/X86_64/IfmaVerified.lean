import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.IfmaCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTP
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtImplies

/-!
# `vg_rsa_private_crt_ifma` on x86-64: verified against the shared contract

`main`'s parts are constant time (those of `vg_rsa_private_crt`, and the
IFMA branch's), so the function is (`ifmaCode_constantTime`); with
correctness (`ifmaCode_correct`) and the contract on the registers and the
stack (`crt_implies`), `CrtIfma.code` is verified (`ifma_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt

/-- `vg_rsa_private_crt_ifma` is constant time but for `n`. -/
theorem ifmaCode_constantTime (M : Mont)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtContract.pre crtContract.pub (CrtIfma.code M.mm) :=
  ifmaCode_constantTime_of M setup_ct checks_ct
    (qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct (gPow_ct_Q M) (redc_ct_Y M) (redc_ct_X M) loadArr_ct_pI hpost

/-- `vg_rsa_private_crt_ifma` with Montgomery multiplication `M`, given that
its code but the vector code never loads MXCSR (which the registration file
evaluates). -/
theorem ifma_verified (M : Mont)
    (hfront : (seqs (nSetup M.mm ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm ++ pPhase M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (CrtIfma.code M.mm) (Spec.Rsa.privateCrtContract abi) :=
  Verified.of_correct (ifmaCode_correct M hfront hpre hpost hcrt) (ifmaCode_constantTime M hpost) crt_implies

end VG.Proof.Bignum.X86_64
