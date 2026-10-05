import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.Ocb.Spec

/-!
# OCB: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean. A write of a byte or of
bytes into a buffer replaces those of its bytes (`bytesAt_writeBytes_at`,
`bytesAt_writeW8_at`), on every target: the pieces build the blocks
`pad(S)` and `Nonce` as lists. A byte of memory as an element of the bytes read
(`getD_bytesAt_eq`), an element of a list of 16 with one byte replaced
(`getD_set16`), bytes XORed with the first bytes of a block
(`xor_bytesAt_block`), and its first bytes (`bytesAt_take_block`).
-/

namespace VG.Proof.Ocb

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

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
theorem bytesAt_writeW8_at (m : Mem) (p : Addr) {o n : Nat} (b : Byte) (h : o + 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) b) p n = (bytesAt m p n).take o ++ [b] ++ (bytesAt m p n).drop (o + 1) := by
  rw [writeW8_eq, bytesAt_writeBytes_at _ _ _ h hn]; rfl

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := bytesAt_writeBytes_at m p (o := 0) xs (by omega) hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [show min k L.length = k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega, ↓reduceIte]
    congr 2; omega

theorem xor_append_right (xs ys zs : List Byte) (h : xs.length = ys.length) :
    Spec.Ocb.xor xs (ys ++ zs) = Spec.Ocb.xor xs ys := by
  simpa [Spec.Ocb.xor] using List.zipWith_append (f := fun x1 x2 : Byte => x1 ^^^ x2) (l₁' := []) (l₂' := zs) h

/-- `r` bytes XORed with the first `r` bytes of a block. -/
theorem xor_bytesAt_block (xs : List Byte) (m : Mem) (Q : Addr) {r : Nat} (hl : xs.length = r) (hr : r ≤ 16) :
    Spec.Ocb.xor xs (bytesAt m Q r) = Spec.Ocb.xor xs (Spec.Ocb.toBytes (Spec.Ocb.blockAtMem m Q)) := by
  rw [Spec.Ocb.blockAtMem, toBytes_ofBytes (Proof.Cmac.bytesAt_length _ _ _), show (16 : Nat) = r + (16 - r) by omega,
    bytesAt_append, xor_append_right _ _ _ (by rw [hl, Proof.Cmac.bytesAt_length])]

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (Spec.Ocb.blockAtMem m p)).take t := by
  rw [Spec.Ocb.blockAtMem, toBytes_ofBytes (Proof.Cmac.bytesAt_length _ _ _), show (16 : Nat) = t + (16 - t) by omega,
    bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.Ocb
