module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Seed
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Sha3.Arith

/-! # The concrete words of a padded 33-byte noise seed -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG

def seedState (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.State := Vector.ofFn fun i : Fin 25 =>
  if i.val < 4 then m.readW (p+BitVec.ofNat 64 (8*i.val)) 64
  else if i.val = 4 then BitVec.ofNat 64 (n+0x1f00)
  else if i.val = 16 then 0x8000000000000000 else 0

theorem tail_byte : ∀ n < 256, ∀ k < 8,
    (BitVec.ofNat 64 (n+0x1f00)).extractLsb' (8*k) 8 =
      if k = 0 then BitVec.ofNat 8 n else if k = 1 then 0x1f else 0 := by decide +kernel

theorem pad_byte : ∀ k < 8, (0x8000000000000000 : BitVec 64).extractLsb' (8*k) 8 =
    if k = 7 then 0x80 else 0 := by decide +kernel

theorem seedState_get (m : Mem) (p : Addr) (n : Nat) {i : Nat} (hi : i < 25) :
    (seedState m p n)[i]! = if i < 4 then m.readW (p+BitVec.ofNat 64 (8*i)) 64
      else if i = 4 then BitVec.ofNat 64 (n+0x1f00) else if i = 16 then 0x8000000000000000 else 0 := by
  rw [getElem!_pos _ i hi]
  unfold seedState
  rw [Vector.getElem_ofFn]

theorem seedBytes_get (m : Mem) (p : Addr) (n j : Nat) :
    (Spec.Sha3.bytesAt m p 32 ++ [BitVec.ofNat 8 n]).getD j 0 =
      if j < 32 then m (p+BitVec.ofNat 64 j) else if j = 32 then BitVec.ofNat 8 n else 0 := by
  by_cases hj : j < 32
  · rw [ite_eq_left hj, List.getD_eq_getElem?_getD, List.getElem?_append_left
      (by rw [Proof.Sha3.bytesAt_length]; exact hj)]
    exact Proof.MlKem.bytesAt_getD m p hj
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append,
      Proof.Sha3.bytesAt_length, ite_eq_right hj]
    by_cases he : j = 32
    · subst j; simp
    · have hne : j - 32 ≠ 0 := by omega
      simp [he, hne]

theorem seedState_eq (m : Mem) (p : Addr) {n : Nat} (hn : n < 256) :
    seedState m p n = Seed.A0 (Spec.Sha3.bytesAt m p 32 ++ [BitVec.ofNat 8 n]) := by
  apply Proof.Sha3.ext_bytes
  intro j hj
  rw [Seed.byteOf_A0 (by simp [Proof.Sha3.bytesAt_length]) hj]
  unfold Proof.Sha3.byteOf
  rw [seedState_get m p n (by omega)]
  by_cases h32 : j < 32
  · rw [ite_eq_left (by omega : j/8 < 4), ite_eq_left (by omega : j < 33), seedBytes_get,
      ite_eq_left h32]
    change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _
    rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
      show 8*(j/8)+j%8 = j by omega]
  · rw [ite_eq_right (by omega : ¬ j/8 < 4)]
    by_cases h40 : j < 40
    · rw [ite_eq_left (by omega : j/8 = 4),tail_byte n hn (j%8) (by omega)]
      rcases (show j = 32 ∨ j = 33 ∨ 34 ≤ j by omega) with h | h | h
      · subst j; rw [ite_eq_left (by decide : 32 < 33), seedBytes_get]; simp
      · subst j; simp
      · simp (disch := omega) only [ite_eq_right]
    · rw [ite_eq_right (by omega : ¬ j/8 = 4)]
      by_cases h16 : j/8 = 16
      · rw [ite_eq_left h16,pad_byte (j%8) (by omega)]
        by_cases he : j = 135 <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
      · rw [ite_eq_right h16]
        simp (disch := omega) only [ite_eq_right]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp

end VG.Proof.MlKem.AArch64.Noise
