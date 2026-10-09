import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLastStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSixthSetup

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (bReg)

private theorem sixthSetup_rows {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 5 σ L s) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeSetup 840 1)) s fun t =>
      Rows v 5 σ L t ∧ t.gpr .x22=stateP σ 0 ∧ t.gpr .x23=stateP σ 1 ∧
      (∀k<4,t.gpr (bReg k)=lastPtr σ k) ∧ t.gpr .x28=1 := by
  refine WP.mono (sixthSetup_ok s) fun t ⟨ht,h22,h23,hbuf,h28⟩ => ?_
  refine ⟨h.of_control ht ?_,?_,?_,?_,h28⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [h22,h.env.x19]
    change scr σ=scr σ+BitVec.ofNat 64 0
    simp
  · rw [h23,h.env.x19]; rfl
  · intro k hk
    rw [hbuf k hk,h.env.x19,lastPtr_eq]
    congr 2
    omega

theorem sixthFour_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.step 840 1) s (Rows 4 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Four.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,h23,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastFour_step_ok hp ha h22 h23
    (hbuf 0 (by decide)) (hbuf 1 (by decide)) (hbuf 2 (by decide)) (hbuf 3 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

theorem sixthTwo_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step 840 1) s (Rows 2 6 σ L) := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.squeezeN
  apply WP.seq
  refine WP.mono (sixthSetup_rows h) fun a ⟨ha,h22,_,hbuf,h28⟩ => ?_
  obtain ⟨tr,t,he,ht,hc⟩ := lastTwo_step_ok hp ha h22 (hbuf 0 (by decide)) (hbuf 1 (by decide)) h28
  exact ⟨_,t,.loopExit he hc,ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
