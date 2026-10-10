import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePacked
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedLanes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseArithmetic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldSchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailBank

/-! ## From `InverseBankFieldPacked.lean` -/

section

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

end

/-! ## From `InverseBankFieldPackedField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedResult_field (a b : BitVec 128) (w : Poly) {len start : Nat}
    (hl : len=1 ∨ len=2) (hstart : start+8≤256) (second : Bool) (root : Nat → Nat)
    {e : Nat} (he : e<4) {bound : Int} (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound)
    (hf : ∀ i<8,ofInt (pairWord a b i).toInt=w[start+i]!) :
    ofInt (vword (packedResult len second a b (fun e => (negZetaNat (root e) : Int))) e).toInt=
      (InverseTraversal.run (InverseTraversal.packedSchedule start len root) w)[start+(if second then 4 else 0)+e]! := by
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  rw [packedResult_int a b hl second _ he hb hs hv,Nat.add_assoc,
    InverseTraversal.packedSchedule_get w hl hstart hi]
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,ofInt_add,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc]
  · rw [ite_eq_right hc,ite_eq_right hc,fastMul_field,ofInt_sub,
      InverseTraversal.ofInt_negZetaNat,hf _ hd.1,hf _ hd.2.1,Nat.add_assoc,Fin.mul_comm]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedBank.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem packedValues_field (v : Vector (BitVec 128) 8) (w : Poly) {g len u : Nat}
    (hg : g<4) (hl : len=1 ∨ len=2) (hu : u<8) (root : Nat → Nat) {bound : Int}
    (hb : 8380417≤bound) (hs : 2*bound<2147483648)
    (hv : ∀ j<8, -bound≤(pairWord v[2*g] v[2*g+1] j).toInt ∧
      (pairWord v[2*g] v[2*g+1] j).toInt≤bound)
    (hf : InnerBankField u v w) :
    InnerBankField u (packedValues v ⟨2*g,by omega⟩ ⟨2*g+1,by omega⟩ len
      (fun e => (negZetaNat (root e) : Int)))
      (InverseTraversal.run (InverseTraversal.packedSchedule (32*u+8*g) len root) w) := by
  intro i e he
  simp only [packedValues,Vector.getElem_set]
  by_cases hj : 2*g+1=i.val
  · rw [ite_eq_left hj]
    have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
      true root he hb hs hv
      (fun i hi => pairWord_field v w hg hf hi)
    simpa only [ite_true,Traversal.innerLoc,← hj,show 32*u+4*(2*g+1)+e=32*u+8*g+4+e by omega] using h
  · rw [ite_eq_right hj]
    by_cases hi : 2*g=i.val
    · rw [ite_eq_left hi]
      have h := packedResult_field v[2*g] v[2*g+1] w hl (show 32*u+8*g+8≤256 by omega)
        false root he hb hs hv
        (fun i hi => pairWord_field v w hg hf hi)
      simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Traversal.innerLoc,← hi,
        show 4*(2*g)=8*g by omega] using h
    · rw [ite_eq_right hi,InverseTraversal.packedSchedule_outside w hl (by omega)
        (by unfold Traversal.innerLoc; omega) (by unfold Traversal.innerLoc; omega),hf i e he]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
