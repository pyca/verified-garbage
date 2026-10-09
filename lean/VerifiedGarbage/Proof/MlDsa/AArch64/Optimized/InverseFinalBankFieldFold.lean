import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem scaleValues_word (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    vword (scaleValues v)[k.val] e=
      if k.val<4 then fastMulWord (vword v[k.val] e) 16382 else vword v[k.val] e := by
  simp only [scaleValues,Vector.getElem_ofFn]
  split
  · exact fastVector_word _ _ he
  · rfl

theorem final_sides (k : Fin 8) : (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) := by
  exact (show ∀ k : Fin 8, (leftSide 6 k.val ↔ k.val<4) ∧ (rightSide 6 k.val ↔ ¬k.val<4) by decide +kernel) k

theorem folded_root_field : ofInt (finalZ 6 0)=ofInt (negZetaNat 1 : Int)*ofInt 16382 := by decide +kernel

theorem folded_lane (v : Vector (BitVec 128) 8) (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=ofInt (vword (stageValues 6 v (fun _ => (negZetaNat 1 : Int)))[k.val] e).toInt*ofInt 16382 := by
  dsimp only
  rw [scaleValues_word _ _ he,stageValues_word _ _ _ _ he]
  simp only [(final_sides k).1,(final_sides k).2]
  by_cases hk : k.val<4
  · rw [ite_eq_left hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := (16382 : Int))
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e+vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,ite_eq_left ((final_sides k).1.mpr hk)]
  · rw [ite_eq_right hk,ite_eq_right hk,ite_eq_left hk]
    have hb := fastMul_bounds (z := finalZ 6 e)
      (BitVec.le_toInt (vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
      (BitVec.toInt_lt (x := vword v[(leftSource 6 k).val] e-vword v[(rightSource 6 k).val] e))
    rw [fastMulWord_int]
    refine ⟨hb.1,hb.2,?_⟩
    rw [fastMul_field,stageValues_word _ _ _ _ he,
      ite_eq_right (fun h => hk ((final_sides k).1.mp h)),ite_eq_left ((final_sides k).2.mpr hk),
      fastMulWord_int,fastMul_field]
    change _*ofInt (finalZ 6 0)=_
    rw [folded_root_field,Fin.mul_assoc]

theorem foldedStage_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : StageBound v 6 268173344) (hf : BankField u v w)
    (k : Fin 8) {e : Nat} (he : e<4) :
    let x := vword (scaleValues (stageValues 6 v (finalZ 6)))[k.val] e;
    -8380417<x.toInt ∧ x.toInt<2*8380417 ∧
      ofInt x.toInt=(InverseTraversal.run (stridedStageOps u 1 6) w)[InverseTraversal.stridedLoc u k.val e]!*ofInt 16382 := by
  have h := folded_lane v k he
  have hs := stridedStageValues_field (6 : Fin 7) v w hu 1 (by decide) (by decide) hv hf k e he
  exact ⟨h.1,h.2.1,h.2.2.trans (congrArg (·*ofInt 16382) hs)⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
