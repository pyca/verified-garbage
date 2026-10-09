import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The physical packed groups and renamed groups visit exactly the logical
local slice, retaining each root index symbolically. -/
theorem fiveOps_eq {u : Nat} (hu : u<8) :
    packedPassOps u ++ runOps u (localIndex u) 0 7=InverseTraversal.localSlice u := by
  exact (show ∀ u : Fin 8,
    packedPassOps u.val ++ runOps u.val (localIndex u.val) 0 7=InverseTraversal.localSlice u.val
    by decide +kernel) ⟨u,hu⟩

/-- The selected five-layer machine bank has the exact inverse field result,
with every signed representative bounded by 32q. No normalization is added. -/
theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (fiveValues u v) 268173344 ∧
      InnerBankField u (fiveValues u v) (InverseTraversal.run (InverseTraversal.localSlice u) w) := by
  rw [fiveValues,packedPassValues_eq]
  have hp := packedPass_field v w hu hv hf
  have h := runValues_local _ _ hu hp.1 hp.2
  refine ⟨h.1,?_⟩
  simpa only [← InverseTraversal.run_append,fiveOps_eq hu] using h.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
