import VerifiedGarbage.Proof.P256.EcdhJac.Masked
import VerifiedGarbage.Proof.P256.EcdhJac.Doubles

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

theorem step_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k j : Nat} (hP : onCurve C P=true)
    (hj : 1≤j) (hj52 : j≤51) {s : State} (hs : LoopInv base P k j s) :
    WP isa Impl.P256.EcdhJac.step s fun t => Frame base work s t ∧ LoopInv base P k (j-1) t := by
  obtain ⟨⟨Q,hQ,hq,rs⟩,s19⟩ := hs
  unfold Impl.P256.EcdhJac.step
  apply WP.seq
  refine WP.mono (decCounter_ok s hj (by omega) s19) fun a ⟨a19,ka⟩ => ?_
  have fa : Frame base work s a := (AllocatedFrame.of_keeps ka).widenRegs (by decide)
  have ra := rs.of_keeps ka (by decide)
  apply WP.seq
  refine WP.mono (doubles_ok hC ha hQ (by omega) ra a19) fun b ⟨fb,rb,b19⟩ => ?_
  have qb : k<C.n → mul 32 Q=mul (32*Window5.winE (k+offset) 52 ((j-1)+1)) P := by
    intro hk
    rw [hq hk,Window5.mul_mul hC hP,show j-1+1=j by omega]
  apply WP.seq
  refine WP.mono (entry_ok (fun _ h => h) (by decide) rb.field rb.fixed rb.table (by omega) b19)
    fun e he => ?_
  have re := he.rstate rb
  have e19 := he.counter.trans b19
  apply WP.seq
  refine WP.mono (add_state re he.field he.cache2 (by
    rw [he.cache3,he.cache2]; exact Lean.Grind.CommSemiring.mul_comm _ _)) fun d hd => ?_
  have d19 := (hd.frame.regs.gpr _ allocatedRegs_x19).trans e19
  have ep : 1≤digitMagnitude k (j-1) →
      InvJ C (tmv C 4 base d K.E.x) (tmv C 4 base d K.E.y) (tmv C 4 base d K.E.z)
        (Window5.winPt C P (k+offset) (j-1)) ∧ tmv C 4 base d K.E.z≠0 := by
    intro hn
    have hp := he.point hn
    rw [hd.same _ (by decide),hd.same _ (by decide),hd.same _ (by decide)]
    exact ⟨hp.jac,hp.z⟩
  refine WP.mono (masked_ok hC ha hO hP (hC.onCurve_mul hQ _) qb hd.state
    (by omega) d19 hd.field ep hd.point) fun t ⟨ft,ht⟩ => ?_
  exact ⟨(((fa.trans fb).trans he.frame).trans (hd.frame.widenRegs allocated_regs)).trans ft,ht⟩

theorem loop_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} (hP : onCurve C P=true)
    {s : State} (hs : LoopInv base P k 51 s) :
    WP isa (.loop Impl.P256.EcdhJac.step (.nonzero .x .x19)) s fun t =>
      Frame base work s t ∧ LoopInv base P k 0 t := by
  apply countLoop_ok (Inv:=fun j t => Frame base work s t ∧ LoopInv base P k j t)
    (n:=51) (by decide)
  · intro j t hj hj51 ⟨fr,hi⟩
    exact WP.mono (step_ok hC ha hO hP hj hj51 hi) fun u ⟨fu,hu⟩ =>
      ⟨⟨fr.trans fu,hu⟩,hu.counter⟩
  · exact fun _ h => h
  · decide
  · exact ⟨AllocatedFrame.refl _ _ _ _,hs⟩

end VG.Proof.P256.EcdhJac
