import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-SIV: masking the data

`decrypt` ANDs the data with the mask of the comparison of the IVs, `0 − 1`
(all ones) or `0`, which leaves the plaintext or zeros: a word and a byte of
it at a time (`mask_word`, `mask_succ`). Nothing here depends on a target.
-/

namespace VG.Proof.AesSiv

open VG VG.WriteBytes

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_length]

/-- The next byte, ANDed with the mask. -/
theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, Proof.Cmac.bytesAt_succ, List.replicate_succ']

/-- The next word, ANDed with the mask. -/
theorem mask_word (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then Spec.Aes.bytesAt m P (j + 8) else Spec.Siv.zeros (j + 8)) =
      (if c then Spec.Aes.bytesAt m P j else Spec.Siv.zeros j) ++
        Proof.Cmac.le8 (m.readW (P + BitVec.ofNat 64 j) 64 &&& (0 - if c then 1 else 0)) := by
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show (0 : BitVec 64) - 0 = 0 from rfl,
      show m.readW (P + BitVec.ofNat 64 j) 64 &&& 0 = 0 from BitVec.and_zero,
      show Proof.Cmac.le8 0 = Spec.Siv.zeros 8 by decide,
      Spec.Siv.zeros, Spec.Siv.zeros, Spec.Siv.zeros, ← List.replicate_append_replicate]
  · simp only [↓reduceIte]
    rw [show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, Proof.Cmac.le8_readW,
      Proof.Cmac.Stream.bytesAt_append]

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW_le8 (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (Proof.Cmac.le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

end VG.Proof.AesSiv
