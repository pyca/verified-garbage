import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedLanes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

/-- The packed inverse gather/scatter computes four ordered scalar butterflies. -/
theorem packedResult_word (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) :
    vword (packedResult len second a b z) e =
      let i := (if second then 4 else 0)+e
      let x := pairWord a b (packedLow len i)
      let y := pairWord a b (packedLow len i+len)
      if i%(2*len)<len then x+y else fastMulWord (x-y) (z (packedLane len i)) := by
  have he' : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases hl with rfl | rfl <;> cases second <;>
    rcases he' with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [packedResult,gather,scatter,
      vword_trn1_d2,vword_trn2_d2,vword_zip1_s4',vword_zip2_s4,
      VG.AArch64.vword_map2,fastVector_word,vword_uzp1_s4,vword_uzp2_s4,
      pairWord,packedLow,packedLane]

/-- Bounds are needed only for the two selected registers, not the other six
registers whose current layer may already have completed. -/
theorem packedResult_int (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    (vword (packedResult len second a b z) e).toInt =
      let i := (if second then 4 else 0)+e
      let x := (pairWord a b (packedLow len i)).toInt
      let y := (pairWord a b (packedLow len i+len)).toInt
      if i%(2*len)<len then x+y else fastMul (x-y) (z (packedLane len i)) := by
  rw [packedResult_word a b hl second z he]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  have hp := pair_word (z := z (packedLane len ((if second then 4 else 0)+e)))
    _ _ hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc]
    exact hp.1
  · rw [ite_eq_right hc,ite_eq_right hc]
    exact hp.2

theorem packedResult_bound (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hq : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    -(2*bound)≤(vword (packedResult len second a b z) e).toInt ∧
      (vword (packedResult len second a b z) e).toInt≤2*bound := by
  rw [packedResult_int a b hl second z he hq hs hv]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  have hp := pair_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    hq hs (hv _ hd.1) (hv _ hd.2.1)
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc]
    simpa only [pair,Int.neg_mul] using hp.1
  · rw [ite_eq_right hc]
    simpa only [pair,Int.neg_mul] using hp.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
