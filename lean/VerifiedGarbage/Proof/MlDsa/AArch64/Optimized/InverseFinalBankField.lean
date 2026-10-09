import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankFieldCanonical

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The selected strided final pass returns canonical coefficients and applies
exactly the last three inverse layers with the folded Montgomery scale. -/
theorem finalValues_field (v : Vector (BitVec 128) 8) (qv : BitVec 128) (w : Poly)
    {u : Nat} (hu : u<8) (hv : BankBound v 268173344) (hf : BankField u v w)
    (hq : ∀ e<4, vword qv e=8380417#32) (i : Fin 8) {e : Nat} (he : e<4) :
    (vword (finalValues v qv)[i.val] e).toNat<8380417 ∧
      ofInt (vword (finalValues v qv)[i.val] e).toInt=
        (InverseTraversal.run (InverseTraversal.stridedSlice u) w)[4*u+32*i.val+e]! * 16382 := by
  have hp := runValues_final_six 0 6 (by decide) v w hu
    ((stageBound_zero v 268173344).mpr hv) hf
  have hl := foldedStage_field _ _ hu hp.1 hp.2 i he
  have hc := canonicalValues_lane _ qv i he (hq e he) hl.1 hl.2.1
  rw [finalValues,runValues_split_last]
  refine ⟨hc.1,hc.2.trans ?_⟩
  simpa only [← InverseTraversal.run_append,stridedOps_eq hu,
    InverseTraversal.stridedLoc,show 32*i.val+4*u+e=4*u+32*i.val+e by omega,
    show ofInt (16382 : Int)=(16382 : Zq) by decide +kernel] using hl.2.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
