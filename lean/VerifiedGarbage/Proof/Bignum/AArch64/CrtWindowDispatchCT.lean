module

import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowConstantTime
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatch
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowConstantTime
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowDispatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowMainCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTNSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTFin
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (eval_zero)

abbrev OldStage := VG.Proof.Bignum.AArch64.Stage VG.Proof.Bignum.AArch64.R0

theorem baselineMain_ct (M : Mont) : RelCT isa (Two OldStage) (VG.Impl.Rsa.AArch64.Crt.main M.mm)
    (fun _ _ => True) :=
  VG.Proof.Bignum.AArch64.crtMain_ct M (VG.Proof.Bignum.AArch64.nSetup_ct M)
    VG.Proof.Bignum.AArch64.setup_ct checks_ct
    (VG.Proof.Bignum.AArch64.qPhase_ct M (unit_ct M (gPow_ct_Q M) (redc_ct_Y M) (by taint_decide))
      (VG.Proof.Bignum.AArch64.pow_ct M (redc_ct_Y M) (expLoop_ct_Q M) (by taint_decide)))
    (VG.Proof.Bignum.AArch64.pPhase_ct M (unit_ct M (gPow_ct_P M) (redc_ct_Y M) (by taint_decide))
      (VG.Proof.Bignum.AArch64.pow_ct M (redc_ct_Y M) (expLoop_ct_P M) (by taint_decide))
      (redc_ct_X M) loadArr_ct_pI)
    VG.Proof.Bignum.AArch64.crtFinish_ct

def GuardPost (p : CrtPub) (s : State) : Prop := OldStage p s ∧ s.gpr .x9 = guardValue p.k p.pl p.ql

theorem guard_post {p : CrtPub} {s : State} (h : OldStage p s) :
    WP isa (.block VG.Impl.Rsa.AArch64.WindowFive.lengthGuard) s (GuardPost p) := by
  obtain ⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,rfl⟩ := h
  exact WP.mono (lengthGuard_ok h) fun t ⟨h9,hm,kk⟩ =>
    ⟨⟨t,xb,pb,qb,dpb,dqb,qib,pre_keep h hm kk,hv,rfl⟩,h9⟩

theorem guarded_wide {p : CrtPub} {s : State}
    (h : GuardPost p s ∧ isa.eval (.zero .x .x9) s = some false) : Stage R0 p s := by
  obtain ⟨⟨⟨σ,xb,pb,qb,dpb,dqb,qib,h,hv,rfl⟩,h9⟩,he⟩ := h
  have hk64 : p.k < 2 ^ 64 := by have := h.k2; omega
  rw [eval_zero,h9] at he
  have hk128 : 128 ≤ p.k := guardValue_nonzero hk64 (Option.some.inj he)
  have hwide : CrtWindowFive.offQ32 p.w p.pl + slot (wsWords p.ql) 8 + CrtWindowFive.tabBytes32 (wsWords p.ql) ≤ p.Z :=
    Nat.le_trans (CrtWindowFive.prime_scratch32_fits hk128 h.pl2 h.ql2) (by have := h.zk; omega)
  exact ⟨s,xb,pb,qb,dpb,dqb,qib,⟨h,hwide⟩,hv,rfl⟩

theorem dispatch_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two OldStage) (VG.Impl.Rsa.AArch64.WindowFive.dispatch W.code S.code M.mm)
      (fun _ _ => True) := by
  unfold VG.Impl.Rsa.AArch64.WindowFive.dispatch
  refine RelCT.seq (two_piece (Ψ := GuardPost) [.x0]
    (pins_x0B CrtPub.B fun _ _ ⟨_,_,_,_,_,_,_,h,_,rfl⟩ => h.x0)
    (by taint_decide) fun _ _ h => guard_post h) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero,eval_zero,h₁.2,h₂.2]) ?_ ?_
  · exact two_map id (fun _ _ h => h.1.1) (baselineMain_ct M)
  · exact two_map id (fun _ _ h => guarded_wide h) (main_ct W M S)

end VG.Proof.Bignum.AArch64.WindowFive
