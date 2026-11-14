module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackTail
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.AArch64.Optimized.HighPackTailWords`, which only this module used -/

section

/-! ### `MlDsa.AArch64.Optimized.HighPackTailMath`, which only this module used -/

section

@[expose] public section

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
  rw [packed4, pack4Vector_byte _ _ (by omega_arith), uzp1_byte _ _ (by omega_arith),
    uzp2_byte _ _ (by omega_arith), ite_eq_left hi, ite_eq_left hi]

private theorem narrowByte (b : BitVec 8) : (b.setWidth 128).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Byte interleaving used to widen pairs before six-bit packing. -/
theorem zip1_byte (x y : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) i = if i % 2 = 0 then vbyte x (i/2) else vbyte y (i/2) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_map, List.length_range,
    vbyte_ofVBytes _ hi, Nat.reduceDiv]
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, ite_true, ite_false, narrowByte]

/-- A 32-bit lane consists of four little-endian bytes. -/
theorem vword_bytes (x : BitVec 128) (j : Nat) :
    vword x j = vbyte x (4*j+3) ++ vbyte x (4*j+2) ++ vbyte x (4*j+1) ++ vbyte x (4*j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases h0 : b < 8
  · simp only [h0, ite_true, decide_true, Bool.true_and]
    congr 1; omega_arith
  by_cases h1 : b < 16
  · simp only [h0, ite_false, show b-8<8 by omega_arith, ite_true, decide_true, Bool.true_and]
    congr 1; omega_arith
  by_cases h2 : b < 24
  · simp only [h0, ite_false, show ¬ b-8<8 by omega_arith, show b-8-8<8 by omega_arith,
      ite_true, decide_true, Bool.true_and]
    congr 1 <;> omega_arith
  · simp only [h0, ite_false, show ¬ b-8<8 by omega_arith, show ¬ b-8-8<8 by omega_arith,
      show b-8-8-8<8 by omega_arith, decide_true, Bool.true_and]
    congr 1; omega_arith

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
  rw [zip1_byte _ _ (by omega_arith), zip1_byte _ _ (by omega_arith),
    zip1_byte _ _ (by omega_arith), zip1_byte _ _ (by omega_arith)]
  have h0 : (4*j)%2=0 := by omega_arith
  have h1 : (4*j+1)%2=1 := by omega_arith
  have h2 : (4*j+2)%2=0 := by omega_arith
  have h3 : (4*j+3)%2=1 := by omega_arith
  simp only [h0,h1,h2,h3, show ¬ (1:Nat)=0 by decide, ite_true, ite_false,
    show (4*j+2)/2=2*j+1 by omega_arith, show (4*j)/2=2*j by omega_arith]
  simp [vbyte]

def mask24 : BitVec 128 := ofVDwords 0xffff0504ffff0100 0xffff0d0cffff0908
def mask25 : BitVec 128 := ofVDwords 0xffff0706ffff0302 0xffff0f0effff0b0a
def mask29 : BitVec 128 := ofVDwords 0x0908060504020100 0xffffffff0e0d0c0a

theorem mask24_index {i : Nat} (hi : i < 16) :
    (vbyte mask24 i).toNat = (if i%4<2 then 4*(i/4)+i%4 else 255) := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mask25_index {i : Nat} (hi : i < 16) :
    (vbyte mask25 i).toNat = (if i%4<2 then 4*(i/4)+i%4+2 else 255) := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mask29_index {i : Nat} (hi : i < 16) :
    (vbyte mask29 i).toNat = (if i<12 then 4*(i/3)+i%3 else 255) := by
  rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem compact_byte (x : BitVec 128) {i : Nat} (hi : i < 12) :
    vbyte (tableBytes x mask29) i = vbyte x (4*(i/3)+i%3) := by
  rw [tableBytes_byte _ _ (by omega_arith), mask29_index (by omega_arith), ite_eq_left hi,
    ite_eq_left (by omega_arith)]

theorem table24_word (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (tableBytes x mask24) j =
      (0 : BitVec 16) ++ (vword x j).extractLsb' 0 16 := by
  rw [vword_bytes]
  rw [tableBytes_byte _ _ (by omega_arith), tableBytes_byte _ _ (by omega_arith),
    tableBytes_byte _ _ (by omega_arith), tableBytes_byte _ _ (by omega_arith)]
  rw [mask24_index (by omega_arith), mask24_index (by omega_arith),
    mask24_index (by omega_arith), mask24_index (by omega_arith)]
  have hm0 : (4*j)%4=0 := by omega_arith
  have hm1 : (4*j+1)%4=1 := by omega_arith
  have hm2 : (4*j+2)%4=2 := by omega_arith
  have hm3 : (4*j+3)%4=3 := by omega_arith
  simp only [hm0,hm1,hm2,hm3, Nat.reduceLT, ite_true, ite_false]
  rw [ite_eq_left (by omega_arith), ite_eq_left (by omega_arith)]
  rw [show 4*((4*j+1)/4)+1=4*j+1 by omega_arith, show 4*(4*j/4)+0=4*j by omega_arith]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    vword, vbyte]
  by_cases h0 : b<8
  · simp only [h0, ite_true, show b<16 by omega_arith, decide_true, Bool.true_and, Nat.zero_add, show b<32 by omega_arith]
    congr 1 <;> omega_arith
  by_cases h1 : b<16
  · simp only [h0, ite_false, show b-8<8 by omega_arith, ite_true, h1, decide_true, Bool.true_and,
      Nat.zero_add, show b<32 by omega_arith]
    congr 1 <;> omega_arith
  · simp only [h0, ite_false, show ¬b-8<8 by omega_arith, h1, decide_false, Bool.false_and]
    simp
theorem table25_word (x : BitVec 128) {j : Nat} (hj : j < 4) :
    vword (tableBytes x mask25) j =
      (0 : BitVec 16) ++ (vword x j).extractLsb' 16 16 := by
  rw [vword_bytes]
  rw [tableBytes_byte _ _ (by omega_arith), tableBytes_byte _ _ (by omega_arith),
    tableBytes_byte _ _ (by omega_arith), tableBytes_byte _ _ (by omega_arith)]
  rw [mask25_index (by omega_arith), mask25_index (by omega_arith),
    mask25_index (by omega_arith), mask25_index (by omega_arith)]
  have hm0 : (4*j)%4=0 := by omega_arith
  have hm1 : (4*j+1)%4=1 := by omega_arith
  have hm2 : (4*j+2)%4=2 := by omega_arith
  have hm3 : (4*j+3)%4=3 := by omega_arith
  simp only [hm0,hm1,hm2,hm3, Nat.reduceLT, ite_true, ite_false]
  rw [ite_eq_left (by omega_arith), ite_eq_left (by omega_arith)]
  rw [show 4*((4*j+1)/4)+1+2=4*j+3 by omega_arith, show 4*(4*j/4)+0+2=4*j+2 by omega_arith]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    vword, vbyte]
  by_cases h0 : b<8
  · simp only [h0, ite_true, show b<16 by omega_arith, show 16+b<32 by omega_arith, decide_true, Bool.true_and]
    congr 1 <;> omega_arith
  by_cases h1 : b<16
  · simp only [h0, ite_false, show b-8<8 by omega_arith, ite_true, h1, show 16+b<32 by omega_arith, decide_true, Bool.true_and]
    congr 1 <;> omega_arith
  · simp only [h0, ite_false, show ¬b-8<8 by omega_arith, h1, decide_false, Bool.false_and]
    simp

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

end


@[expose] public section

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
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31) with
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
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', hb, show 8*r+b<32 by omega_using [hr, hb],
    decide_true, Bool.true_and]
  congr 1; omega_using []

theorem pack6Vector_byte (e o : BitVec 128) {i : Nat} (hi : i<12) :
    vbyte (pack6Vector e o 0 mask24 mask25 mask29) i =
      (sixWord (vbyte e (2*(i/3))) (vbyte o (2*(i/3)))
        (vbyte e (2*(i/3)+1)) (vbyte o (2*(i/3)+1))).extractLsb' (8*(i%3)) 8 := by
  change vbyte (tableBytes (groups6 e o) mask29) i = _
  rw [compact_byte _ hi, vbyte_word _ _ (by omega_using []), groups6_word _ _ (by omega_using [hi])]

/-- The six-bit tail packs each four coefficients into three little-endian bytes. -/
theorem packed6_byte (s : State) (hz : s.v .v28=0) (h24 : s.v .v24=mask24)
    (h25 : s.v .v25=mask25) (h29 : s.v .v29=mask29) {i : Nat} (hi : i<12) :
    vbyte (packed6 s) i =
      (sixWord (vbyte (gathered s) (4*(i/3))) (vbyte (gathered s) (4*(i/3)+1))
        (vbyte (gathered s) (4*(i/3)+2)) (vbyte (gathered s) (4*(i/3)+3))).extractLsb' (8*(i%3)) 8 := by
  rw [packed6, hz, h24, h25, h29, pack6Vector_byte _ _ hi,
    uzp1_byte _ _ (by omega_using [hi]), uzp2_byte _ _ (by omega_using [hi]),
    uzp1_byte _ _ (by omega_using [hi]), uzp2_byte _ _ (by omega_using [hi]),
    ite_eq_left (by omega_using [hi] : 2*(i/3)<8), ite_eq_left (by omega_using [hi] : 2*(i/3)+1<8)]
  rw [show 2*(2*(i/3))=4*(i/3) by omega_using [],
    show 2*(2*(i/3)+1)=4*(i/3)+2 by omega_using [],
    show 4*(i/3)+2+1=4*(i/3)+3 by omega_using []]
  rw [ite_eq_left (by omega_using [hi]), ite_eq_left (by omega_using [hi])]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64
open VG.Proof.MlKem (digits digits_cons digits_nil)

private theorem or_shift_add {a : Nat} (k b : Nat) (ha : a<2^k) :
    a ||| (b <<< k)=a+b*2^k := by
  rw [Nat.or_comm,←Nat.shiftLeft_add_eq_or_of_lt ha,Nat.shiftLeft_eq,Nat.add_comm]

/-- Bounded four-bit fields occupy disjoint nibbles, so OR is exact addition. -/
theorem nibble_value (a b : BitVec 8) (ha : a.toNat<16) (hb : b.toNat<16) :
    (a ||| (b <<< 4)).toNat=a.toNat+16*b.toNat := by
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft]
  have hmod : (b.toNat <<< 4)%2^8=b.toNat <<< 4 := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    omega_using [hb]
  rw [hmod,or_shift_add 4 b.toNat ha]
  omega_using []

/-- Four six-bit coefficients form exactly one 24-bit base-64 integer. -/
theorem sixWord_value (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) :
    (sixWord a b c d).toNat=a.toNat+64*b.toNat+4096*c.toNat+262144*d.toNat := by
  simp only [sixWord,BitVec.toNat_or,BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (by decide : 8≤32)]
  have m6 : (b.toNat <<< 6)%2^32=b.toNat <<< 6 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  have m12 : (c.toNat <<< 12)%2^32=c.toNat <<< 12 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  have m18 : (d.toNat <<< 18)%2^32=d.toNat <<< 18 := by
    apply Nat.mod_eq_of_lt; rw [Nat.shiftLeft_eq]; omega
  rw [m6,m12,m18,or_shift_add 6 b.toNat ha,
    or_shift_add 12 c.toNat (by omega),or_shift_add 18 d.toNat (by omega)]
  omega

theorem nibble_digits (a b : BitVec 8) (ha : a.toNat<16) (hb : b.toNat<16) :
    a ||| (b <<< 4)=BitVec.ofNat 8 (digits 4 [a.toNat,b.toNat]) := by
  apply BitVec.eq_of_toNat_eq
  rw [nibble_value a b ha hb]
  simp only [digits_cons,digits_nil,Nat.mul_zero,Nat.add_zero,BitVec.toNat_ofNat]
  omega_using [ha, hb]

theorem sixWord_digits (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) :
    (sixWord a b c d).toNat=digits 6 [a.toNat,b.toNat,c.toNat,d.toNat] := by
  rw [sixWord_value a b c d ha hb hc hd]
  simp only [digits_cons,digits_nil,Nat.mul_zero,Nat.add_zero]
  omega_using []


/-- Extracting a stored byte agrees with the byte of the specification's
four-coefficient integer. -/
theorem sixWord_byte_digits (a b c d : BitVec 8)
    (ha : a.toNat<64) (hb : b.toNat<64) (hc : c.toNat<64) (hd : d.toNat<64) (i : Nat) :
    (sixWord a b c d).extractLsb' (8*i) 8 =
      BitVec.ofNat 8 (digits 6 [a.toNat,b.toNat,c.toNat,d.toNat]/2^(8*i)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb',
    Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
  rw [sixWord_digits a b c d ha hb hc hd]

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
