import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHashPadding
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailFirst
import VerifiedGarbage.Proof.MlKem.Mem

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.Spec.Sha3 VG.Proof.Sha3

theorem firstState_byte (m : Mem) (mu w1 : Addr) {j : Nat} (hj : j<200) :
    byteOf (firstState m mu w1) j=
      if j<64 then m (mu+BitVec.ofNat 64 j)
      else if j<136 then m (w1+BitVec.ofNat 64 (j-64)) else 0 := by
  rw [byteOf_eq' _ hj]
  simp only [firstState,Vector.getElem_ofFn]
  by_cases h64 : j<64
  · rw [ite_eq_left (by omega : j/8<8),ite_eq_left h64]
    simp only [Mem.readW,BitVec.setWidth_eq]
    rw [Mem.extractLsb'_read _ _ (by omega : j%8<64/8)]
    simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬j/8<8),ite_eq_right h64]
    by_cases h136 : j<136
    · rw [ite_eq_left (by omega : j/8<17),ite_eq_left h136]
      simp only [Mem.readW,BitVec.setWidth_eq]
      rw [Mem.extractLsb'_read _ _ (by omega : j%8<64/8)]
      simp only [laneAddr,BitVec.add_assoc,←BitVec.ofNat_add,show 8*(j/8-8)+j%8=j-64 by omega]
    · rw [ite_eq_right (by omega : ¬j/8<17),ite_eq_right h136]
      exact BitVec.extractLsb'_zero

theorem firstState_eq (m : Mem) (mu w1 : Addr) :
    firstState m mu w1=xorBytes zero (bytesAt m mu 64++bytesAt m w1 72) := by
  apply ext_bytes
  intro j hj
  rw [firstState_byte m mu w1 hj,byteOf_xorBytes _ _ hj]
  have hz : byteOf zero j=0 := by
    rw [byteOf_eq' _ hj]
    simp [zero]
  rw [hz]
  change _=(0#8) ^^^ _
  rw [BitVec.zero_xor]
  by_cases h64 : j<64
  · rw [ite_eq_left h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map,List.getElem?_range h64,Option.map_some,Option.getD_some]
  · rw [ite_eq_right h64]
    simp only [bytesAt,List.getD_eq_getElem?_getD,List.getElem?_append,List.length_map,List.length_range,
      h64,↓reduceIte,List.getElem?_map]
    by_cases h136 : j<136
    · rw [ite_eq_left h136,List.getElem?_range (by omega : j-64<72)]
      rfl
    · rw [ite_eq_right h136,List.getElem?_eq_none (by simp;omega)]
      rfl

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
