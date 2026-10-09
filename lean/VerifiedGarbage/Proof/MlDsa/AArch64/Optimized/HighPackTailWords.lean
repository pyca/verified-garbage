import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTailMath

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

def sixWord (a b c d : BitVec 8) : BitVec 32 :=
  a.setWidth 32 ||| (b.setWidth 32 <<< 6) ||| (c.setWidth 32 <<< 12) ||| (d.setWidth 32 <<< 18)

def spaced (a b : BitVec 8) : BitVec 32 := (0 : BitVec 8) ++ b ++ (0 : BitVec 8) ++ a

/-- Each lane's two 12-bit pairs compact to a 24-bit group. -/
theorem joinSixWord (a b c d : BitVec 8) :
    let p := spaced a c ||| (spaced b d <<< 6)
    ((0 : BitVec 16) ++ p.extractLsb' 0 16) |||
      (((0 : BitVec 16) ++ p.extractLsb' 16 16) <<< 12) = sixWord a b c d := by
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [spaced, sixWord, HAppend.hAppend, BitVec.append, BitVec.getLsbD_setWidth', BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
      Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, Nat.zero_add, 
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true,
      Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false]
  all_goals simp

def pairs6 (e o : BitVec 128) : BitVec 128 :=
  VPermOp.eval .zip1 .b16 e 0 ||| wordShift 6 (VPermOp.eval .zip1 .b16 o 0)

def groups6 (e o : BitVec 128) : BitVec 128 :=
  tableBytes (pairs6 e o) mask24 ||| wordShift 12 (tableBytes (pairs6 e o) mask25)

theorem pairs6_word (e o : BitVec 128) {j : Nat} (hj : j<4) :
    vword (pairs6 e o) j = spaced (vbyte e (2*j)) (vbyte e (2*j+1)) |||
      (spaced (vbyte o (2*j)) (vbyte o (2*j+1)) <<< 6) := by
  unfold pairs6
  rw [show vword (VPermOp.eval .zip1 .b16 e 0 ||| wordShift 6 (VPermOp.eval .zip1 .b16 o 0)) j =
    vword (VPermOp.eval .zip1 .b16 e 0) j ||| vword (wordShift 6 (VPermOp.eval .zip1 .b16 o 0)) j from
    BitVec.extractLsb'_or]
  rw [zipZero_word _ hj, wordShift_word _ _ hj, zipZero_word _ hj]
  rfl

theorem groups6_word (e o : BitVec 128) {j : Nat} (hj : j<4) :
    vword (groups6 e o) j = sixWord (vbyte e (2*j)) (vbyte o (2*j))
      (vbyte e (2*j+1)) (vbyte o (2*j+1)) := by
  unfold groups6
  rw [show vword (tableBytes (pairs6 e o) mask24 ||| wordShift 12 (tableBytes (pairs6 e o) mask25)) j =
    vword (tableBytes (pairs6 e o) mask24) j ||| vword (wordShift 12 (tableBytes (pairs6 e o) mask25)) j from
    BitVec.extractLsb'_or]
  rw [table24_word _ hj, wordShift_word _ _ hj, table25_word _ hj, pairs6_word _ _ hj]
  exact joinSixWord _ _ _ _

/-- An arbitrary byte within a 32-bit lane. -/
theorem vbyte_word (x : BitVec 128) (j : Nat) {r : Nat} (hr : r<4) :
    vbyte x (4*j+r) = (vword x j).extractLsb' (8*r) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', hb, show 8*r+b<32 by omega,
    decide_true, Bool.true_and]
  congr 1; omega

theorem pack6Vector_byte (e o : BitVec 128) {i : Nat} (hi : i<12) :
    vbyte (pack6Vector e o 0 mask24 mask25 mask29) i =
      (sixWord (vbyte e (2*(i/3))) (vbyte o (2*(i/3)))
        (vbyte e (2*(i/3)+1)) (vbyte o (2*(i/3)+1))).extractLsb' (8*(i%3)) 8 := by
  change vbyte (tableBytes (groups6 e o) mask29) i = _
  rw [compact_byte _ hi, vbyte_word _ _ (by omega), groups6_word _ _ (by omega)]

/-- The six-bit tail packs each four coefficients into three little-endian bytes. -/
theorem packed6_byte (s : State) (hz : s.v .v28=0) (h24 : s.v .v24=mask24)
    (h25 : s.v .v25=mask25) (h29 : s.v .v29=mask29) {i : Nat} (hi : i<12) :
    vbyte (packed6 s) i =
      (sixWord (vbyte (gathered s) (4*(i/3))) (vbyte (gathered s) (4*(i/3)+1))
        (vbyte (gathered s) (4*(i/3)+2)) (vbyte (gathered s) (4*(i/3)+3))).extractLsb' (8*(i%3)) 8 := by
  rw [packed6, hz, h24, h25, h29, pack6Vector_byte _ _ hi,
    uzp1_byte _ _ (by omega), uzp2_byte _ _ (by omega),
    uzp1_byte _ _ (by omega), uzp2_byte _ _ (by omega),
    ite_eq_left (by omega : 2*(i/3)<8), ite_eq_left (by omega : 2*(i/3)+1<8)]
  rw [show 2*(2*(i/3))=4*(i/3) by omega,
    show 2*(2*(i/3)+1)=4*(i/3)+2 by omega,
    show 4*(i/3)+2+1=4*(i/3)+3 by omega]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
