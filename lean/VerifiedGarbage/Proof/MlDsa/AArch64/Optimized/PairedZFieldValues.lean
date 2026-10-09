import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckOutput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

/-- The fused z store is the same centered representative on successful and
unsuccessful attempts. -/
theorem zOutput_field {raw low high : BitVec 128} (c : CheckConstants)
    {e : Nat} (he : e<4) (hl : (vword low e).toNat<8380417)
    (hr : -8380417<(vword raw e).toInt ∧ (vword raw e).toInt<2*8380417) :
    let x := vword (checkOutput false raw low high c) e;
    -4202495≤x.toInt ∧ x.toInt≤4210685 ∧
      ofInt x.toInt=ofInt ((vword low e).toNat+(vword raw e).toInt) := by
  simp only [checkOutput,laneVector_word _ he,Bool.false_eq_true,ite_false]
  rw [BitVec.add_comm (vword raw e),addReduced_int _ _ hl hr]
  have hb := reduce32_bounds (by omega : -2*8380417<(vword low e).toNat+(vword raw e).toInt)
    (by omega : (vword low e).toNat+(vword raw e).toInt<3*8380417)
  exact ⟨hb.1,hb.2,reduce32_field _⟩

end VG.Proof.MlDsa.AArch64.Optimized.Paired
