import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedBank

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64

/-- A packed layer doubles the bound only for the register pairs it has
already processed; the following pair still has the old bound. -/
def PackedProgress (v : Vector (BitVec 128) 8) (g : Nat) (b : Int) : Prop :=
  ∀ i : Fin 8, ∀ e<4,
    -(if i.val<2*g then 2*b else b)≤(vword v[i.val] e).toInt ∧
      (vword v[i.val] e).toInt≤(if i.val<2*g then 2*b else b)

theorem PackedProgress.pair {v : Vector (BitVec 128) 8} {g : Nat} {b : Int}
    (h : PackedProgress v g b) (hg : g<4) {i : Nat} (hi : i<8) :
    -b≤(pairWord v[2*g] v[2*g+1] i).toInt ∧ (pairWord v[2*g] v[2*g+1] i).toInt≤b := by
  unfold pairWord
  split
  · have hv := h ⟨2*g,by omega⟩ i ‹_›
    simpa only [show ¬2*g<2*g by omega,ite_false] using hv
  · have hv := h ⟨2*g+1,by omega⟩ (i-4) (by omega)
    simpa only [show ¬2*g+1<2*g by omega,ite_false] using hv

theorem packedValues_progress (v : Vector (BitVec 128) 8) {g len : Nat} (hg : g<4)
    (hl : len=1 ∨ len=2) (z : Nat → Int) {b : Int} (hb : 8380417≤b)
    (hs : 2*b<2147483648) (hv : PackedProgress v g b) :
    PackedProgress (packedValues v ⟨2*g,by omega⟩ ⟨2*g+1,by omega⟩ len z) (g+1) b := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj,ite_eq_left (by omega : i.val<2*(g+1))]
    exact packedResult_bound _ _ hl true z he hb hs (fun j hj => hv.pair hg hj)
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi,ite_eq_left (by omega : i.val<2*(g+1))]
      exact packedResult_bound _ _ hl false z he hb hs (fun j hj => hv.pair hg hj)
    · rw [ite_eq_right hi]
      have heq : (i.val<2*(g+1)) ↔ (i.val<2*g) := by omega
      simpa only [heq] using hv i e he

theorem packedProgress_zero (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 0 b ↔ BankBound v b := by
  simp only [PackedProgress,BankBound,Nat.mul_zero,Nat.not_lt_zero,ite_false]

theorem packedProgress_four (v : Vector (BitVec 128) 8) (b : Int) :
    PackedProgress v 4 b ↔ BankBound v (2*b) := by
  constructor <;> intro h i e he
  all_goals have hi : i.val<2*4 := i.isLt
  · simpa only [hi,ite_true] using h i e he
  · simpa only [hi,ite_true] using h i e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
