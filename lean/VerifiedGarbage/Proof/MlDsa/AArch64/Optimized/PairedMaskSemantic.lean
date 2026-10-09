import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedPassFlags
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZ

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Optimized.Response

theorem normMask_zero {x : BitVec 32} {B : Nat} (hB : 1≤B) (hB' : B≤524288)
    (hl : -8380417<x.toInt) (hh : x.toInt<8380417) :
    normMask x (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      -(B:Int)<x.toInt ∧ x.toInt<(B:Int) := by
  rw [normMask_value hB hB' hl hh]
  split
  · rename_i h
    exact ⟨fun _ => h,fun _ => rfl⟩
  · rename_i h
    exact ⟨fun hz => False.elim ((by decide : (-1 : BitVec 32)≠0) hz),
      fun hx => False.elim (h hx)⟩

/-- The z machine mask is zero exactly at the specification's strict norm. -/
theorem zMask_zero {a b : BitVec 32} {B : Nat} (ha : a.toNat<8380417)
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord (b+a)) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      normZq (ofInt ((a.toNat:Int)+b.toInt))<B := by
  rw [BitVec.add_comm b a]
  have hi := addReduced_int a b ha hb
  have bounds := reduce32_bounds (by omega : -2*8380417<(a.toNat:Int)+b.toInt)
    (by omega : (a.toNat:Int)+b.toInt<3*8380417)
  rw [normMask_zero hB hB' (by rw [hi]; omega) (by rw [hi]; omega),hi]
  exact (reduce32_norm_iff _ _ (by omega) (by omega) hB').symm

/-- The hint path checks the inverse product itself against the strict bound. -/
theorem hMask_zero {b : BitVec 32} {B : Nat}
    (hb : -8380417<b.toInt ∧ b.toInt<2*8380417) (hB : 1≤B) (hB' : B≤524288) :
    normMask (reduceWord b) (BitVec.ofNat 32 (B-1)) (BitVec.ofNat 32 (2*B-1))=0 ↔
      normZq (ofInt b.toInt)<B := by
  have hi := reduceWord_int b (by omega) (by omega)
  have bounds := reduce32_bounds (by omega : -2*8380417<b.toInt)
    (by omega : b.toInt<3*8380417)
  rw [normMask_zero hB hB' (by rw [hi]; omega) (by rw [hi]; omega),hi]
  exact (reduce32_norm_iff _ _ (by omega) (by omega) hB').symm

end VG.Proof.MlDsa.AArch64.Optimized.Paired
