import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def finalIndex (i : Nat) : Nat := if i<4 then 7-i else if i<6 then 3-(i-4) else 1

def stridedRunOps (u i : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => stridedStageOps u (finalIndex i) i ++ stridedRunOps u (i+1) n

theorem finalZ_index {i : Nat} (hi : i<6) : finalZ i=(fun _ => (negZetaNat (finalIndex i) : Int)) := by
  funext e
  simp only [finalZ,finalValue,finalIndex]
  split
  · rfl
  · rfl

theorem runValues_final_six (i n : Nat) (hin : i+n≤6) (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : StageBound v i 268173344) (hf : BankField u v w) :
    StageBound (runValues finalZ i n v) (i+n) 268173344 ∧
      BankField u (runValues finalZ i n v) (InverseTraversal.run (stridedRunOps u i n) w) := by
  induction n generalizing i v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hi : i<6 := by omega
    have hp := stageValues_bound ⟨i,by omega⟩ v (finalZ i) (by decide) (by decide) hv
    have hfield := stridedStageValues_field ⟨i,by omega⟩ v w hu (finalIndex i) (by decide) (by decide) hv hf
    rw [← finalZ_index hi] at hfield
    have h := ih (i := i+1) (by omega) _ _ hp hfield
    simpa only [runValues,stridedRunOps,InverseTraversal.run_append,Nat.add_assoc,Nat.add_comm 1 n] using h

theorem stridedOps_eq {u : Nat} (hu : u<8) :
    stridedRunOps u 0 6 ++ stridedStageOps u 1 6=InverseTraversal.stridedSlice u := by
  exact (show ∀ u : Fin 8,
    stridedRunOps u.val 0 6 ++ stridedStageOps u.val 1 6=InverseTraversal.stridedSlice u.val
    by decide +kernel) ⟨u,hu⟩

theorem runValues_split_last (v : Vector (BitVec 128) 8) :
    runValues finalZ 0 7 v=stageValues 6 (runValues finalZ 0 6 v) (finalZ 6) := rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
