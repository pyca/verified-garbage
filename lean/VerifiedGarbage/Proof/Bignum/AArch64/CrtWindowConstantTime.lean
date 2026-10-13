module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTCode

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupFix
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowFinCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupFix
import Mathlib.Data.Int.ModEq
meta import Mathlib.Data.Int.ModEq

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
