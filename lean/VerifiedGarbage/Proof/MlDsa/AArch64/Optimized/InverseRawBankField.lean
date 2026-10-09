import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRawFinalSlice

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- Omitting the final correction retains the exact field result in the
strict signed Barrett interval. -/
theorem rawFinalValues_field (v : Vector (BitVec 128) 8) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (i : Fin 8) {e : Nat} (he : e<4) :
    -8380417<(vword (rawFinalValues v)[i.val] e).toInt ∧
      (vword (rawFinalValues v)[i.val] e).toInt<2*8380417 ∧
      ofInt (vword (rawFinalValues v)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  rw [rawFinalValues,runValues_split_last]
  refine ⟨hl.1,hl.2.1,?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega,
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
