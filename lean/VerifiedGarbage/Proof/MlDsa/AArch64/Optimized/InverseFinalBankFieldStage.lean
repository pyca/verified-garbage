import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldGroups

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def stridedStageOps (u root i : Nat) : List InverseTraversal.Op :=
  InverseTraversal.stridedRegGroupSchedule u (2*steps[i]!.1*steps[i]!.2) steps[i]!.1 root

theorem stridedStageValues_field (i : Fin 7) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (root : Nat) {b : Int}
    (hb : 8380417≤b) (hs : 8*b<2147483648) (hv : StageBound v i.val b)
    (hf : BankField u v w) :
    BankField u (stageValues i.val v (fun _ => (negZetaNat root : Int)))
      (InverseTraversal.run (stridedStageOps u root i.val) w) := by
  intro k e he
  rw [stageValues_word _ _ _ _ he]
  change ofInt (_ : BitVec 32).toInt =
    (InverseTraversal.run (stridedStageOps u root i.val) w)[InverseTraversal.stridedLoc u k.val e]!
  rw [stridedStageOps,InverseTraversal.run_stridedRegGroup,
    InverseTraversal.stridedRegBlock_get _ (step_bounds i).1 (step_bounds i).2 hu (Nat.le_refl _) _ k.isLt he]
  rw [show 2*steps[i.val]!.1*steps[i.val]!.2+steps[i.val]!.1+steps[i.val]!.1=
      2*steps[i.val]!.1*steps[i.val]!.2+2*steps[i.val]!.1 by omega]
  change ofInt (_ : BitVec 32).toInt =
    if leftSide i.val k.val then
      w[InverseTraversal.stridedLoc u k.val e]! + w[InverseTraversal.stridedLoc u (k.val+steps[i.val]!.1) e]!
    else if rightSide i.val k.val then -zetas root *
      (w[InverseTraversal.stridedLoc u (k.val-steps[i.val]!.1) e]! - w[InverseTraversal.stridedLoc u k.val e]!)
    else w[InverseTraversal.stridedLoc u k.val e]!
  have hg := stage_depth_geometry i k
  have hsrc := source_geometry i k
  by_cases ha : leftSide i.val k.val ∨ rightSide i.val k.val
  · rw [ite_eq_left ha] at hg
    have hl := hv (leftSource i.val k) e he
    have hr := hv (rightSource i.val k) e he
    rw [← hg.1] at hr
    have hsafe := stage_bound_safe hb hs hg.2.2
    have hw := pair_word (vword v[(leftSource i.val k).val] e)
      (vword v[(rightSource i.val k).val] e) (negZetaNat root : Int) hsafe.1 hsafe.2 hl hr
    have hleft := hf (leftSource i.val k) e he
    have hright := hf (rightSource i.val k) e he
    by_cases hL : leftSide i.val k.val
    · rw [ite_eq_left hL] at hsrc
      rw [ite_eq_left hL,hw.1]
      simp only [pair]
      rw [ofInt_add,hleft,hright,ite_eq_left hL]
      simp only [Traversal.loc,InverseTraversal.stridedLoc,hsrc.1,hsrc.2]
    · have hR := ha.resolve_left hL
      rw [ite_eq_right hL,ite_eq_left hR] at hsrc
      rw [ite_eq_right hL,ite_eq_left hR,hw.2]
      simp only [pair]
      rw [fastMul_field,ofInt_sub,InverseTraversal.ofInt_negZetaNat,hleft,hright,
        ite_eq_right hL,ite_eq_left hR,Fin.mul_comm]
      simp only [Traversal.loc,InverseTraversal.stridedLoc,hsrc.1,hsrc.2]
  · rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    rw [ite_eq_right (fun h => ha (Or.inl h)),ite_eq_right (fun h => ha (Or.inr h))]
    exact hf k e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
