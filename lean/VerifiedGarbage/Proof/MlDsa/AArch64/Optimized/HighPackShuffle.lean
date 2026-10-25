module

public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.HighPack
open VG VG.AArch64

private theorem narrowByte (b : BitVec 8) : (b.setWidth 128).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- UZP selects alternating bytes across the concatenated source registers. -/
theorem uzp1_byte (x y : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (VPermOp.eval .uzp1 .b16 x y) i =
      if i < 8 then vbyte x (2*i) else vbyte y (2*(i-8)) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_map, List.length_range,
    vbyte_ofVBytes _ hi, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  split
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some, narrowByte]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.length_map, List.length_range,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, narrowByte]
    congr 1; omega

theorem uzp2_byte (x y : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (VPermOp.eval .uzp2 .b16 x y) i =
      if i < 8 then vbyte x (2*i+1) else vbyte y (2*(i-8)+1) := by
  simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_map, List.length_range,
    vbyte_ofVBytes _ hi, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  split
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some, narrowByte]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.length_map, List.length_range,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some, narrowByte]
    congr 1; omega

def gatherBytes (x y : BitVec 128) : BitVec 128 :=
  let t := VPermOp.eval .uzp1 .b16 x y
  VPermOp.eval .uzp1 .b16 t t

/-- Two byte-unzips gather the low bytes of eight 32-bit coefficients. -/
theorem gatherBytes_low (x y : BitVec 128) {i : Nat} (hi : i < 8) :
    vbyte (gatherBytes x y) i = if i < 4 then vbyte x (4*i) else vbyte y (4*(i-4)) := by
  dsimp only [gatherBytes]
  rw [uzp1_byte _ _ (by omega), ite_eq_left hi, uzp1_byte _ _ (by omega)]
  by_cases h : i < 4
  · rw [ite_eq_left (by omega), ite_eq_left h]
    congr 1
    omega
  · rw [ite_eq_right (by omega), ite_eq_right h]
    congr 1
    omega

/-- Concatenate the low eight bytes of each input register. -/
theorem zip1_dword_byte (x y : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (VPermOp.eval .zip1 .d2 x y) i = if i < 8 then vbyte x i else vbyte y (i-8) := by
  have hz : VPermOp.eval .zip1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
    simp only [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceDiv, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil,
      List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append]
    congr 1 <;> rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [hz]
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : i < 8
  · simp only [h, ite_true, show 8*i+t<64 by omega, vdword, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  · simp only [h, ite_false, show ¬ 8*i+t<64 by omega, vdword, BitVec.getLsbD_extractLsb',
      show 8*i+t-64<64 by omega, ht, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
    congr 1
    omega

def gatherSixteen (a b c d : BitVec 128) : BitVec 128 :=
  VPermOp.eval .zip1 .d2 (gatherBytes a b) (gatherBytes c d)

/-- The five initial shuffle instructions collect exactly sixteen low bytes. -/
theorem gatherSixteen_byte (a b c d : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (gatherSixteen a b c d) i =
      if i < 4 then vbyte a (4*i) else if i < 8 then vbyte b (4*(i-4))
      else if i < 12 then vbyte c (4*(i-8)) else vbyte d (4*(i-12)) := by
  unfold gatherSixteen
  rw [zip1_dword_byte _ _ hi]
  by_cases h8 : i < 8
  · rw [ite_eq_left h8, gatherBytes_low _ _ h8]
    by_cases h4 : i < 4
    · rw [ite_eq_left h4, ite_eq_left h4]
    · rw [ite_eq_right h4, ite_eq_right h4, ite_eq_left h8]
  · rw [ite_eq_right h8, gatherBytes_low _ _ (by omega),
      ite_eq_right (by omega : ¬ i < 4), ite_eq_right h8]
    by_cases h12 : i < 12
    · rw [ite_eq_left (by omega), ite_eq_left h12]
    · rw [ite_eq_right (by omega), ite_eq_right h12]
      congr 1

end VG.Proof.MlDsa.AArch64.Optimized.HighPack
