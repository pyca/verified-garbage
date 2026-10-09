import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCompact

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def nibbleWord (x : BitVec 128) (i : Nat) : BitVec 32 :=
 ((if i%2=0 then vbyte x (i/2) &&& 15 else vbyte x (i/2) >>> 4) : BitVec 8).setWidth 32

def expandIndices : BitVec 128 := 0xffffff03ffffff02ffffff01ffffff00

private theorem narrowByte (b : BitVec 8) : (b.setWidth 128).setWidth 8=b := by
 rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

theorem zip1_byte (x y : BitVec 128) {i : Nat} (hi : i<16) :
    vbyte (VPermOp.eval .zip1 .b16 x y) i=
      if i%2=0 then vbyte x (i/2) else vbyte y (i/2) := by
  simp only [VPermOp.eval,VArr.lanes,VArr.ofLanes,List.length_map,List.length_range,
    vbyte_ofVBytes _ hi]
  rcases (by omega : i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7∨i=8∨i=9∨i=10∨i=11∨i=12∨i=13∨i=14∨i=15) with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [List.range,List.range.loop,List.map_cons,List.map_nil,List.flatMap_cons,
      List.flatMap_nil,List.cons_append,List.nil_append,List.getD_cons_zero,List.getD_cons_succ,
      Nat.reduceDiv,Nat.reduceMod,Nat.reduceEqDiff,ite_true,ite_false,narrowByte]

def extractVector (x : BitVec 128) : BitVec 128 :=
 tableBytes (VPermOp.eval .zip1 .b16
   (ofVBytes fun i => vbyte x i &&& 15)
   (ofVBytes fun i => vbyte x i >>> 4)) expandIndices

theorem expandIndices_byte : ∀i<4,∀j<4,
    vbyte expandIndices (4*i+j)=if j=0 then BitVec.ofNat 8 i else 255 := by decide

theorem extractVector_byte (x : BitVec 128) {i j : Nat} (hi : i<4) (hj : j<4) :
    vbyte (extractVector x) (4*i+j)=
      if j=0 then (nibbleWord x i).setWidth 8 else 0 := by
  rw [extractVector,tableBytes,vbyte_ofVBytes _ (by omega),expandIndices_byte i hi j hj]
  by_cases hz : j=0
  · subst j
    simp only [ite_true,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show i<256 by omega)]
    rw [ite_eq_left (by omega),zip1_byte _ _ (by omega),
      vbyte_ofVBytes _ (by omega),vbyte_ofVBytes _ (by omega)]
    simp only [nibbleWord]
    split <;> rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]
  · simp only [hz,ite_false]
    rw [ite_eq_right (by decide)]

private theorem widened_byte (b : BitVec 8) {j : Nat} (hj : j<4) :
    vbyte ((b.setWidth 32).setWidth 128) j=if j=0 then b else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [vbyte,BitVec.getLsbD_extractLsb',hk,decide_true,Bool.true_and,
    BitVec.getLsbD_setWidth]
  by_cases hz : j=0
  · subst j
    simp only [Nat.mul_zero,Nat.zero_add,show k<32 by omega,show k<128 by omega,decide_true,
      Bool.true_and,ite_true]
  · have h8 : ¬8*j+k<8 := by omega
    rw [BitVec.getLsbD_of_ge b _ (by omega)]
    simp only [Bool.and_false,hz,ite_false]
    change false=(0#8).getLsbD k
    exact (BitVec.getLsbD_zero).symm

theorem extractVector_word (x : BitVec 128) {i : Nat} (hi : i<4) :
    vword (extractVector x) i=nibbleWord x i := by
  have hh := word_eq_of_bytes (extractVector x) ((nibbleWord x i).setWidth 128) i 0 (by
    intro j hj
    rw [extractVector_byte x hi hj]
    simp only [Nat.mul_zero,Nat.zero_add,nibbleWord]
    rw [widened_byte _ hj]
    rw [BitVec.setWidth_setWidth_of_le _ (show 8≤32 by decide),BitVec.setWidth_eq])
  simpa only [vword,Nat.mul_zero,BitVec.extractLsb'_setWidth_of_le (show 0+32≤128 by decide),
    BitVec.extractLsb'_eq_self] using hh

private theorem lowNibble_eq : ∀ b : BitVec 8,
    (b &&& 15).setWidth 32=BitVec.ofNat 32 (b.toNat%16) := by decide

private theorem highNibble_eq : ∀ b : BitVec 8,
    (b>>>4).setWidth 32=BitVec.ofNat 32 (b.toNat/16) := by decide

theorem nibbleWord_value (x : BitVec 128) (i : Nat) :
    nibbleWord x i=BitVec.ofNat 32
      (if i%2=0 then (vbyte x (i/2)).toNat%16 else (vbyte x (i/2)).toNat/16) := by
  unfold nibbleWord
  split
  · exact lowNibble_eq _
  · exact highNibble_eq _

theorem nibbleWord_bound (x : BitVec 128) (i : Nat) : (nibbleWord x i).toNat<16 := by
  rw [nibbleWord_value,BitVec.toNat_ofNat]
  have hb := (vbyte x (i/2)).isLt
  split <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
