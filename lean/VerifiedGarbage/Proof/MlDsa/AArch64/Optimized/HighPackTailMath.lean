import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTail

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

/-- The four-bit tail stores adjacent coefficients in the low and high nibble. -/
theorem pack4Vector_byte (e o : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (pack4Vector e o) i = vbyte e i ||| (vbyte o i <<< 4) := by
  simp only [pack4Vector, vbyte, BitVec.extractLsb'_or]
  congr 1
  change vbyte (byteShift4 o) i = _
  rw [byteShift4, VArr.map2, vbyte_ofVBytes _ hi]
  rfl

theorem packed4_byte (s : State) {i : Nat} (hi : i < 8) :
    vbyte (packed4 s) i = vbyte (gathered s) (2*i) ||| (vbyte (gathered s) (2*i+1) <<< 4) := by
  rw [packed4, pack4Vector_byte _ _ (by omega), uzp1_byte _ _ (by omega),
    uzp2_byte _ _ (by omega), ite_eq_left hi, ite_eq_left hi]

private theorem narrowByte (b : BitVec 8) : (b.setWidth 128).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Byte interleaving used to widen pairs before six-bit packing. -/
theorem zip1_byte (x y : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) i = if i % 2 = 0 then vbyte x (i/2) else vbyte y (i/2) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_map, List.length_range,
    vbyte_ofVBytes _ hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ite_true, ite_false, narrowByte]

/-- A 32-bit lane consists of four little-endian bytes. -/
theorem vword_bytes (x : BitVec 128) (j : Nat) :
    vword x j = vbyte x (4*j+3) ++ vbyte x (4*j+2) ++ vbyte x (4*j+1) ++ vbyte x (4*j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases h0 : b < 8
  · simp only [h0, ite_true, decide_true, Bool.true_and]
    congr 1; omega
  by_cases h1 : b < 16
  · simp only [h0, ite_false, show b-8<8 by omega, ite_true, decide_true, Bool.true_and]
    congr 1; omega
  by_cases h2 : b < 24
  · simp only [h0, ite_false, show ¬ b-8<8 by omega, show b-8-8<8 by omega,
      ite_true, decide_true, Bool.true_and]
    congr 1 <;> omega
  · simp only [h0, ite_false, show ¬ b-8<8 by omega, show ¬ b-8-8<8 by omega,
      show b-8-8-8<8 by omega, decide_true, Bool.true_and]
    congr 1; omega

theorem wordShift_word (n : Nat) (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (wordShift n x) j = vword x j <<< n := by
  rw [wordShift, vword_map2 _ _ _ hj]
  rfl

theorem tableBytes_byte (x indices : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (tableBytes x indices) i =
      if (vbyte indices i).toNat < 16 then vbyte x (vbyte indices i).toNat else 0 :=
  vbyte_ofVBytes _ hi

theorem zipZero_word (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (VPermOp.eval .zip1 .b16 x 0) j =
      (0 : BitVec 8) ++ vbyte x (2*j+1) ++ (0 : BitVec 8) ++ vbyte x (2*j) := by
  rw [vword_bytes]
  rw [zip1_byte _ _ (by omega), zip1_byte _ _ (by omega),
    zip1_byte _ _ (by omega), zip1_byte _ _ (by omega)]
  have h0 : (4*j)%2=0 := by omega
  have h1 : (4*j+1)%2=1 := by omega
  have h2 : (4*j+2)%2=0 := by omega
  have h3 : (4*j+3)%2=1 := by omega
  simp only [h0,h1,h2,h3, show ¬ (1:Nat)=0 by decide, ite_true, ite_false,
    show (4*j+2)/2=2*j+1 by omega, show (4*j)/2=2*j by omega]
  simp [vbyte]

def mask24 : BitVec 128 := ofVDwords 0xffff0504ffff0100 0xffff0d0cffff0908
def mask25 : BitVec 128 := ofVDwords 0xffff0706ffff0302 0xffff0f0effff0b0a
def mask29 : BitVec 128 := ofVDwords 0x0908060504020100 0xffffffff0e0d0c0a

theorem mask24_index {i : Nat} (hi : i < 16) :
    (vbyte mask24 i).toNat = (if i%4<2 then 4*(i/4)+i%4 else 255) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mask25_index {i : Nat} (hi : i < 16) :
    (vbyte mask25 i).toNat = (if i%4<2 then 4*(i/4)+i%4+2 else 255) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mask29_index {i : Nat} (hi : i < 16) :
    (vbyte mask29 i).toNat = (if i<12 then 4*(i/3)+i%3 else 255) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem compact_byte (x : BitVec 128) {i : Nat} (hi : i < 12) :
    vbyte (tableBytes x mask29) i = vbyte x (4*(i/3)+i%3) := by
  rw [tableBytes_byte _ _ (by omega), mask29_index (by omega), ite_eq_left hi,
    ite_eq_left (by omega)]

theorem table24_word (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (tableBytes x mask24) j =
      (0 : BitVec 16) ++ (vword x j).extractLsb' 0 16 := by
  rw [vword_bytes]
  rw [tableBytes_byte _ _ (by omega), tableBytes_byte _ _ (by omega),
    tableBytes_byte _ _ (by omega), tableBytes_byte _ _ (by omega)]
  rw [mask24_index (by omega), mask24_index (by omega),
    mask24_index (by omega), mask24_index (by omega)]
  have hm0 : (4*j)%4=0 := by omega
  have hm1 : (4*j+1)%4=1 := by omega
  have hm2 : (4*j+2)%4=2 := by omega
  have hm3 : (4*j+3)%4=3 := by omega
  simp only [hm0,hm1,hm2,hm3, Nat.reduceLT, ite_true, ite_false]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  rw [show 4*((4*j+1)/4)+1=4*j+1 by omega, show 4*(4*j/4)+0=4*j by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    vword, vbyte]
  by_cases h0 : b<8
  · simp only [h0, ite_true, show b<16 by omega, decide_true, Bool.true_and, Nat.zero_add, show b<32 by omega]
    congr 1 <;> omega
  by_cases h1 : b<16
  · simp only [h0, ite_false, show b-8<8 by omega, ite_true, h1, decide_true, Bool.true_and,
      Nat.zero_add, show b<32 by omega]
    congr 1 <;> omega
  · simp only [h0, ite_false, show ¬b-8<8 by omega, h1, decide_false, Bool.false_and]
    simp
theorem table25_word (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (tableBytes x mask25) j =
      (0 : BitVec 16) ++ (vword x j).extractLsb' 16 16 := by
  rw [vword_bytes]
  rw [tableBytes_byte _ _ (by omega), tableBytes_byte _ _ (by omega),
    tableBytes_byte _ _ (by omega), tableBytes_byte _ _ (by omega)]
  rw [mask25_index (by omega), mask25_index (by omega),
    mask25_index (by omega), mask25_index (by omega)]
  have hm0 : (4*j)%4=0 := by omega
  have hm1 : (4*j+1)%4=1 := by omega
  have hm2 : (4*j+2)%4=2 := by omega
  have hm3 : (4*j+3)%4=3 := by omega
  simp only [hm0,hm1,hm2,hm3, Nat.reduceLT, ite_true, ite_false]
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  rw [show 4*((4*j+1)/4)+1+2=4*j+3 by omega, show 4*(4*j/4)+0+2=4*j+2 by omega]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    vword, vbyte]
  by_cases h0 : b<8
  · simp only [h0, ite_true, show b<16 by omega, show 16+b<32 by omega, decide_true, Bool.true_and]
    congr 1 <;> omega
  by_cases h1 : b<16
  · simp only [h0, ite_false, show b-8<8 by omega, ite_true, h1, show 16+b<32 by omega, decide_true, Bool.true_and]
    congr 1 <;> omega
  · simp only [h0, ite_false, show ¬b-8<8 by omega, h1, decide_false, Bool.false_and]
    simp

theorem vbyte_lowWord (x : BitVec 128) (i : Nat) :
    vbyte x (4*i) = (vword x i).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    hb, show b<32 by omega, decide_true, Bool.true_and]
  congr 1; omega

/-- Gathered byte indices agree with the four-register lane layout of loadFour_ok. -/
theorem gathered_byte (s : State) {i : Nat} (hi : i<16) :
    vbyte (gathered s) i =
      (vword (s.v ([.v0,.v1,.v2,.v3] : List VReg)[i/4]!) (i%4)).setWidth 8 := by
  rw [gathered, gatherSixteen_byte _ _ _ _ hi]
  by_cases h4 : i<4
  · rw [ite_eq_left h4, vbyte_lowWord, show i/4=0 by omega, show i%4=i by omega]
    rfl
  by_cases h8 : i<8
  · rw [ite_eq_right h4, ite_eq_left h8, vbyte_lowWord,
      show i/4=1 by omega, show i%4=i-4 by omega]
    rfl
  by_cases h12 : i<12
  · rw [ite_eq_right h4, ite_eq_right h8, ite_eq_left h12, vbyte_lowWord,
      show i/4=2 by omega, show i%4=i-8 by omega]
    rfl
  · rw [ite_eq_right h4, ite_eq_right h8, ite_eq_right h12, vbyte_lowWord,
      show i/4=3 by omega, show i%4=i-12 by omega]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
