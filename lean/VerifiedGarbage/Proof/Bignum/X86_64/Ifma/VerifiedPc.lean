module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMainPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTMainPc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCodePc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCodePc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcImplies
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcImplies
import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExpL
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetup
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# RSA with AVX512_IFMA on x86-64, with the precomputed values: verified

`entry`, the modulus' check and `fail` as for `vg_rsa_private_crt`
(`crtFrontPc_ct`) and `main` with `pc` (`mainPc_ct`): the code is constant
time (`codePc_constantTime`), and with its correctness (`codePc_correct`)
and the contract on the registers and the stack (`crtPc_implies`), verified
(`verifiedPc`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.Bignum.X86_64 (crtPcContract crtFrontPc_ct ccRelPc_constantTime setup_ct checks_ct qPhasePc_ct
  pPhasePc_ct gPow_ct_Q gPow_ct_P redc_ct_Y redc_ct_X redc_ct_R2 redc_ct_Xm pow_ct loadArr_ct_pI crtPc_implies)

/-- `vg_rsa_private_crt_precomputed_ifma` is constant time but for `n`. -/
theorem codePc_constantTime (M : Mont)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true) :
    ConstantTime isa crtPcContract.pre crtPcContract.pub (CrtIfma.code M.mm true) := by
  unfold CrtIfma.code
  exact ccRelPc_constantTime (crtFrontPc_ct (mainPc_ct M setup_ct checks_ct
    (qPhasePc_ct M (CrtExpL.w4 M) (gPow_ct_Q M) (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).2
      (by taint_decide)))
    (pPhasePc_ct M (CrtExpL.w4 M) (gPow_ct_P M) (pow_ct M (CrtExpL.w4 M) (redc_ct_Y M) (CrtExpL.w4_ct M).1
      (by taint_decide)) (redc_ct_X M) loadArr_ct_pI)
    (redc_ct_R2 M) (redc_ct_Xm M) loadArr_ct_pI hpost))

/-- `vg_rsa_private_crt_precomputed_ifma` with Montgomery multiplication `M`,
given that its code but the vector code never loads MXCSR (which the
registration file evaluates). -/
theorem verifiedPc (M : Mont)
    (hfront : (seqs (nSetup M.mm true ++ primesSetup ++ checks)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpre : (seqs (CrtIfma.pre M.mm true)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hpost : (seqs (CrtIfma.post M.mm)).allInstrs (fun i => !loadsMxcsr i) = true)
    (hcrt : (seqs (qPhase M.mm (CrtExpL.w4 M).code true ++ pPhase M.mm (CrtExpL.w4 M).code true)).allInstrs
      (fun i => !loadsMxcsr i) = true) :
    Verified target (CrtIfma.code M.mm true) (Spec.Rsa.privateCrtPrecomputedContract abi) :=
  Verified.of_correct (codePc_correct M hfront hpre hpost hcrt) (codePc_constantTime M hpost) crtPc_implies

end VG.Proof.Bignum.X86_64.Ifma
