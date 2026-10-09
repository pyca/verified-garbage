import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalChecked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalSpec
import VerifiedGarbage.Proof.MlDsa.Arith.Montgomery

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem local_run (w : Poly) : run localSchedule w=run standardLocal w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) local_checked w).symm

theorem strided_run (w : Poly) : run stridedSchedule w=run standardStrided w :=
  (Schedule.check_run (fun _ _ h => mask_comm h) strided_checked w).symm

/-- Independent local five-layer blocks followed by strided three-layer slices
are Algorithm 42, before its final coefficient scaling. -/
theorem traversal_nttInv (w : Poly) :
    (run stridedSchedule (run localSchedule w)).map (· * 8347681)=nttInv w := by
  rw [local_run,strided_run,← run_append,standard_inverse]

/-- The selected inverse uses R/256 instead of 1/256, compensating a preceding
Montgomery point product. This changes only the internal representation. -/
theorem traversal_montgomery (w : Poly) :
    (run stridedSchedule (run localSchedule w)).map (· * 16382)=montgomeryNttInv w := by
  rw [montgomeryNttInv,← traversal_nttInv]
  rw [Vector.map_map]
  have h : (8347681 : Zq)*montgomeryR=16382 := by decide +kernel
  simp only [Function.comp_def,Fin.mul_assoc,h]

/-- Folding the final scale into the difference root has exactly the same
field result as uniformly scaling both outputs of the final butterfly. -/
theorem folded_pair (a b z c : Zq) :
    ((a+b)*c,(z*c)*(a-b))=((a+b)*c,(z*(a-b))*c) := by
  congr 1
  rw [Fin.mul_assoc,Fin.mul_comm c,← Fin.mul_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
