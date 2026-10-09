import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailNonceValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSeed

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG

def seedBytes (m : Mem) (p : Addr) (k : BitVec 64) : List Byte :=
  Spec.Sha3.bytesAt m p 64 ++ [k.extractLsb' 0 8,k.extractLsb' 8 8]

theorem seedBytes_length (m : Mem) (p : Addr) (k : BitVec 64) :
    (seedBytes m p k).length=66 := by
  simp only [seedBytes,List.length_append,Proof.Sha3.bytesAt_length,List.length_cons,List.length_nil]

theorem seedBytes_get (m : Mem) (p : Addr) (k : BitVec 64) {j : Nat} (hj : j<66) :
    (seedBytes m p k).getD j 0 = if j<64 then m (p+BitVec.ofNat 64 j)
      else if j=64 then k.extractLsb' 0 8 else k.extractLsb' 8 8 := by
  unfold seedBytes
  by_cases h : j<64
  · rw [ite_eq_left h]
    rw [List.getD,List.getElem?_append_left (by rw [Proof.Sha3.bytesAt_length]; exact h)]
    exact Proof.MlKem.bytesAt_getD m p h
  · rw [ite_eq_right h,List.getD,List.getElem?_append_right (by rw [Proof.Sha3.bytesAt_length]; omega),Proof.Sha3.bytesAt_length]
    rcases (show j=64 ∨ j=65 by omega) with rfl|rfl <;> rfl

theorem seedNonceState_get (m : Mem) (p : Addr) (k : BitVec 64) {i : Nat} (hi : i<25) :
    (seedNonceState m p k)[i]! = if i<8 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i=8 then nonceWord k else if i=16 then 0x8000000000000000 else 0 := by
  rw [Proof.Sha3.getElem!_eq _ hi]
  unfold seedNonceState
  rw [Vector.getElem_ofFn]

theorem seedNonceState_A0 (m : Mem) (p : Addr) (k : BitVec 64) :
    seedNonceState m p k = Optimized.ResidentSeed66.A0 (seedBytes m p k) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Optimized.ResidentSeed66.byteOf_A0 (seedBytes_length m p k) hj]
  unfold Proof.Sha3.byteOf
  rw [seedNonceState_get m p k (by omega)]
  by_cases h32 : j<64
  · rw [ite_eq_left (by omega : j/8<8),ite_eq_left (by omega : j<66),
      seedBytes_get m p k (by omega),ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8=j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8<8)]
    by_cases h40 : j<72
    · rw [ite_eq_left (by omega : j/8=8),nonceWord_byte k (by omega)]
      rcases (show j=64 ∨ j=65 ∨ j=66 ∨ 67≤j by omega) with h|h|h|h
      · subst j
        rw [ite_eq_left (by decide : 64<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j
        rw [ite_eq_left (by decide : 65<66),seedBytes_get m p k (by decide)]
        rfl
      · subst j; simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8=8)]
      by_cases h20 : j/8=16
      · rw [ite_eq_left h20,Optimized.ResidentMask.pad_byte (j%8) (by omega)]
        by_cases he : j=135 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h20]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
