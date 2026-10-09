import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Packed
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def pairWord (a b : BitVec 128) (i : Nat) : BitVec 32 :=
  if i<4 then vword a i else vword b (i-4)

def packedLane (len i : Nat) : Nat := len*(i/(2*len))+i%len

def packedLow (len i : Nat) : Nat := 2*len*(i/(2*len))+i%len

/-- The gather/scatter pair implements four scalar butterflies in coefficient order. -/
theorem packedResult_word (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) :
    vword (packedResult len second a b z) e =
      let i := (if second then 4 else 0)+e
      let x := pairWord a b (packedLow len i)
      let y := fastMulWord (pairWord a b (packedLow len i+len)) (z (packedLane len i))
      if i%(2*len)<len then x+y else x-y := by
  have he' : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases hl with rfl | rfl <;> cases second <;>
    rcases he' with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) [packedResult,gatherWord,scatterWord,show ¬ (1:Nat)=2 by decide,
      vword_trn1_d2,vword_trn2_d2,
      vword_zip1_s4',vword_zip2_s4,
      VG.AArch64.vword_map2,fastVector_word,
      vword_uzp1_s4,vword_uzp2_s4,
      pairWord,packedLow,packedLane]

theorem packed_indices {len i : Nat} (hl : len=1 ∨ len=2) (hi : i<8) :
    packedLow len i<8 ∧ packedLow len i+len<8 ∧ packedLane len i<4 := by
  rcases hl with rfl | rfl <;> unfold packedLow packedLane <;> omega

theorem packedResult_int (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    (vword (packedResult len second a b z) e).toInt =
      let i := (if second then 4 else 0)+e
      let x := (pairWord a b (packedLow len i)).toInt
      let y := fastMul (pairWord a b (packedLow len i+len)).toInt (z (packedLane len i))
      if i%(2*len)<len then x+y else x-y := by
  rw [packedResult_word a b hl second z he]
  have hi : (if second then 4 else 0)+e<8 := by cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  have hx := hv _ hd.1
  have hy := fastMul_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    (BitVec.le_toInt (pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
    (BitVec.toInt_lt (x := pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc,ite_eq_left hc,addWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega),fastMulWord_int]
  · rw [ite_eq_right hc,ite_eq_right hc,subWord_int _ _ (by rw [fastMulWord_int]; omega) (by rw [fastMulWord_int]; omega),fastMulWord_int]

theorem packedResult_bound (a b : BitVec 128) {len : Nat} (hl : len=1 ∨ len=2)
    (second : Bool) (z : Nat → Int) {e : Nat} (he : e<4) {bound : Int}
    (hb : 0≤bound) (hs : bound+16760834<2147483648)
    (hv : ∀ i<8,-bound≤(pairWord a b i).toInt ∧ (pairWord a b i).toInt≤bound) :
    -(bound+16760834)≤(vword (packedResult len second a b z) e).toInt ∧
      (vword (packedResult len second a b z) e).toInt≤bound+16760834 := by
  rw [packedResult_int a b hl second z he hb hs hv]
  have hi : (if second then 4 else 0)+e<8 := by
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.zero_add] <;> omega
  have hd := packed_indices hl hi
  have hx := hv _ hd.1
  have hy := fastMul_bounds (z := z (packedLane len ((if second then 4 else 0)+e)))
    (BitVec.le_toInt (pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
    (BitVec.toInt_lt (x := pairWord a b (packedLow len ((if second then 4 else 0)+e)+len)))
  dsimp only
  by_cases hc : ((if second then 4 else 0)+e)%(2*len)<len
  · rw [ite_eq_left hc]; omega
  · rw [ite_eq_right hc]; omega

end VG.Proof.MlDsa.AArch64.Optimized
