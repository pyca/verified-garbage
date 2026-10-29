module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT


import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Complete constant-time composition of the wider-window CRT computation. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum

theorem nSetup_ct (M : Mont) :
    RelCT isa (Two (Stage R0)) (seqs (nSetup M.mm)) (fun _ _ => True) :=
  two_map id (fun _ _ ⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,hr⟩ =>
    ⟨σ,xb,pb,qb,dpb,dqb,qib,h.toCrtPre,hv,hr⟩) (VG.Proof.Bignum.AArch64.nSetup_ct M)

theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Stage R0))
      (VG.Impl.Rsa.AArch64.WindowFive.main W.code S.code M.mm) (fun _ _ => True) :=
  crtMain_ct W M S (nSetup_ct M) setup_ct checks_ct
    (qPhase_ct W M S (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (pow_ct W M S (redc_ct_Y M) (expLoop_ct W M S (by taint_decide)) (by taint_decide)))
    (pPhase_ct W M S (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (pow_ct W M S (redc_ct_Y M) (expLoop_ct W M S (by taint_decide)) (by taint_decide))
      (redc_ct_X M) loadArr_ct_pI)
    crtFinish_ct

end VG.Proof.Bignum.AArch64.WindowFive
