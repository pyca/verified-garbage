import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-CCM: bytes of a buffer

Untrusted: everything here is checked by Lean, and depends on no target. A
write of bytes into a buffer replaces those of its bytes
(`bytesAt_writeBytes_at`); its prefixes and suffixes; and the
big-endian encodings `[v]₈ₖ` split into zeros and `[v]₈q` (`be_split`).
Shared by the 32-bit (`Bytes`) and 64-bit (`Words`) lemmas.
-/

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n)[i]'(by rw [length_bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

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
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, toNat_ofNat64 (by omega), toNat_ofNat64 (by omega)]
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

theorem bytesAt_prefix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m p a = (bytesAt m p n).take a := by
  rw [show n = a + (n - a) by omega, Proof.Cmac.Stream.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

theorem bytesAt_suffix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m (p + BitVec.ofNat 64 a) (n - a) = (bytesAt m p n).drop a := by
  conv => rhs; rw [show n = a + (n - a) by omega, Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_left' (length_bytesAt _ _ _)]

theorem be_zero (k : Nat) : Spec.Ccm.be k 0 = Spec.Ccm.zeros k := by
  simp [Spec.Ccm.be, Spec.Ccm.zeros, List.map_const']

/-- `[v]₈ₖ` for `v < 2^(8q)` and `k ≥ q`: zeros, then `[v]₈q`. -/
theorem be_split {q k v : Nat} (hqk : q ≤ k) (hv : v < 256 ^ q) :
    Spec.Ccm.be k v = Spec.Ccm.zeros (k - q) ++ Spec.Ccm.be q v := by
  induction k with
  | zero => rw [show q = 0 by omega]; simp [Spec.Ccm.zeros, Spec.Ccm.be]
  | succ k ih =>
    rcases Nat.lt_or_ge k q with h | h
    · rw [show q = k + 1 by omega]; simp [Spec.Ccm.zeros]
    · rw [be_succ, ih h, show k + 1 - q = (k - q) + 1 by omega, Spec.Ccm.zeros, Spec.Ccm.zeros,
        List.replicate_succ, List.cons_append]
      congr 1
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h))]
      rfl

theorem zipWith_or_zeros_right (xs : List Byte) {n : Nat} (h : xs.length = n) :
    List.zipWith (· ||| ·) xs (Spec.Ccm.zeros n) = xs := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

theorem zipWith_or_zeros_left (ys : List Byte) {n : Nat} (h : ys.length = n) :
    List.zipWith (· ||| ·) (Spec.Ccm.zeros n) ys = ys := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

end VG.Proof.AesCcm
