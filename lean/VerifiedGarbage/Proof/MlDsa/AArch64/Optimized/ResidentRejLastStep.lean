import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLastProgress
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Advance

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (RegKeep)
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Spec.MlDsa (Zq)

theorem lastProgress_ok {v p : Nat} {σ s : State} {L : Nat → List Zq} {rp ra rb : Reg}
    (hp : Pre v σ) (h : LastProgress v σ L p s) (hpv : 2*p+1<v)
    (hr : FiveRegisters rp ra rb) (hreg : CallRegs rp ra rb) (hrp : s.gpr rp=stateP σ p)
    (ha : s.gpr ra=lastPtr σ (2*p)) (hb : s.gpr rb=lastPtr σ (2*p+1)) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      LastProgress v σ L (p+1) t ∧ RegKeep blockRegs s t := by
  refine WP.mono (lastPair_ok hp h.env hpv hr hreg
    (by simpa only [Nat.lt_irrefl,ite_false] using h.pairs p hpv) hrp ha hb)
    fun t ⟨he,hs,oa,ob,hf,hg⟩ => ⟨h.next hp hpv he hf hs oa ob,hg⟩

theorem lastAdvance_ok {v : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v 6 σ L s) (h28 : s.gpr .x28=1) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.advance) s fun t =>
      Rows v 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.advance_ok s)
    fun t ⟨ht,_,hcount⟩ => ⟨h.of_control ht ?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · rw [eval_nonzero,hcount,h28]
    rfl

theorem lastFour_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 4 σ) (h : Rows 4 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0) (h23 : s.gpr .x23=stateP σ 1)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h26 : s.gpr .x26=lastPtr σ 2) (h27 : s.gpr .x27=lastPtr σ 3)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.step s fun t =>
      Rows 4 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<4)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  apply WP.seq
  refine WP.mono (lastProgress_ok hp ha (by decide : 2*1+1<4) fiveRegisters1 callRegs1
    (by rw [hga.gpr .x23 (by decide)]; exact h23)
    (by rw [hga.gpr .x26 (by decide)]; exact h26)
    (by rw [hga.gpr .x27 (by decide)]; exact h27)) fun b ⟨hb,hgb⟩ => ?_
  exact lastAdvance_ok (hb.rows (by decide)) (by
    rw [hgb.gpr .x28 (by decide),
      hga.gpr .x28 (by decide),h28])

theorem lastTwo_step_ok {σ s : State} {L : Nat → List Zq}
    (hp : Pre 2 σ) (h : Rows 2 5 σ L s)
    (h22 : s.gpr .x22=stateP σ 0)
    (h24 : s.gpr .x24=lastPtr σ 0) (h25 : s.gpr .x25=lastPtr σ 1)
    (h28 : s.gpr .x28=1) :
    WP isa Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step s fun t =>
      Rows 2 6 σ L t ∧ isa.eval (.nonzero .x .x28) t=some false := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.step
  apply WP.seq
  refine WP.mono (lastProgress_ok hp h.lastProgress (by decide : 2*0+1<2)
    fiveRegisters0 callRegs0 h22 h24 h25) fun a ⟨ha,hga⟩ => ?_
  exact lastAdvance_ok (ha.rows (by decide)) (by
    rw [hga.gpr .x28 (by decide),h28])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
