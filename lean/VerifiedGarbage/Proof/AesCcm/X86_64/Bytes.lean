import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32

/-!
# AES-CCM on x86-64: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean. A write of a byte, a word or
bytes into a buffer replaces those of its bytes (`bytesAt_writeBytes_at`,
`bytesAt_writeW8_at`, `bytesAt_writeW64_at`, `bytesAt_writeW32_at`): the
pieces build their blocks (`Ctr₀`, `B₀`, the first block of the associated
data, a last block padded) as lists.
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8 le4)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n)[i]'(by rw [length_bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

/-- `xs` written at `p + o`, inside the `n` bytes at `p`. -/
theorem bytesAt_writeBytes_at (m : Mem) (p : Addr) {o n : Nat} (xs : List Byte) (h : o + xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p n =
      (bytesAt m p n).take o ++ xs ++ (bytesAt m p n).drop (o + xs.length) := by
  apply List.ext_getElem (by simp [length_bytesAt]; omega)
  intro i h₁ h₂
  rw [getElem_bytesAt _ _ (by rw [length_bytesAt] at h₁; exact h₁)]
  simp only [writeBytes]
  have hi : i < n := by rw [length_bytesAt] at h₁; exact h₁
  have e : (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 o)).toNat = (i + (2 ^ 64 - o)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, toNat_ofNat_of_lt (by omega), toNat_ofNat_of_lt (by omega)]
    omega
  rw [e]
  have hl := length_bytesAt m p n
  by_cases hlo : i < o
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = 2 ^ 64 - o + i by omega]
    simp only [show ¬ (2 ^ 64 - o + i < xs.length) by omega, ite_false]
    rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_left (by simp [hl]; omega),
      List.getElem_take, getElem_bytesAt _ _ hi]
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = i - o by omega]
    by_cases hhi : i < o + xs.length
    · simp only [show i - o < xs.length by omega, ite_true]
      rw [List.getElem_append_left (by simp [hl]; omega), List.getElem_append_right (by simp [hl]; omega)]
      simp only [List.length_take, hl, List.getD_eq_getElem?_getD, Nat.min_eq_left (show o ≤ n by omega),
        List.getElem?_eq_getElem (show i - o < xs.length by omega), Option.getD_some]
    · simp only [show ¬ (i - o < xs.length) by omega, ite_false]
      rw [List.getElem_append_right (by simp [hl]; omega), List.getElem_drop]
      simp only [List.length_append, List.length_take, hl, Nat.min_eq_left (show o ≤ n by omega)]
      rw [getElem_bytesAt _ _ (by omega), show o + xs.length + (i - (o + xs.length)) = i by omega]

/-- A byte write is a write of one byte. -/
theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_cons, List.length_nil, Nat.zero_add]
  split
  · rename_i h
    simp only [show (x - a).toNat = 0 by omega, List.getD_cons_zero]
    simp
  · rfl

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

theorem writeW32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le4 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le4]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le4 _ h]
    simp
  · rfl

theorem bytesAt_writeW8_at (m : Mem) (p : Addr) {o n : Nat} (b : Byte) (h : o + 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) b) p n = (bytesAt m p n).take o ++ [b] ++ (bytesAt m p n).drop (o + 1) := by
  rw [writeW8_eq, bytesAt_writeBytes_at _ _ _ h hn]; rfl

theorem bytesAt_writeW64_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 64) (h : o + 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le8 v ++ (bytesAt m p n).drop (o + 8) := by
  rw [writeW64_eq, bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le8]; exact h) hn, Proof.Cmac.length_le8]

theorem bytesAt_writeW32_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 32) (h : o + 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le4 v ++ (bytesAt m p n).drop (o + 4) := by
  rw [writeW32_eq, bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le4]; exact h) hn, Proof.Cmac.length_le4]

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := bytesAt_writeBytes_at m p (o := 0) xs (by omega) hn
  simpa using this

theorem bytesAt_writeW64_base (m : Mem) (p : Addr) {n : Nat} (v : BitVec 64) (h : 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p v) p n = le8 v ++ (bytesAt m p n).drop 8 := by
  have := bytesAt_writeW64_at m p (o := 0) v h hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

end VG.Proof.AesCcm.X86_64
