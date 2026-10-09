import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-CCM: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean, and depends on no target. A
write of a byte, a 32-bit word or bytes into a buffer replaces those of its
bytes (`bytesAt_writeBytes_at`, `bytesAt_writeW8_at`, `bytesAt_writeW32_at`),
so that the pieces of the 32-bit implementations build their blocks
(`Ctr₀`, `B₀`, the first block of the associated data, a last block padded)
as lists; and `[v]₈ₖ` split into zeros and `[v]₈q` (`be_split`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)

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
  apply List.ext_getElem (by simp [length_bytesAt]; omega_arith)
  intro i h₁ h₂
  rw [getElem_bytesAt _ _ (by rw [length_bytesAt] at h₁; exact h₁)]
  simp only [writeBytes]
  have hi : i < n := by rw [length_bytesAt] at h₁; exact h₁
  have e : (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 o)).toNat = (i + (2 ^ 64 - o)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, toNat_ofNat64 (by omega_arith), toNat_ofNat64 (by omega_arith)]
    omega_arith
  rw [e]
  have hl := length_bytesAt m p n
  by_cases hlo : i < o
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = 2 ^ 64 - o + i by omega_arith]
    simp only [show ¬ (2 ^ 64 - o + i < xs.length) by omega_arith, ite_false]
    rw [List.getElem_append_left (by simp [hl]; omega_arith), List.getElem_append_left (by simp [hl]; omega_arith),
      List.getElem_take, getElem_bytesAt _ _ hi]
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = i - o by omega_arith]
    by_cases hhi : i < o + xs.length
    · simp only [show i - o < xs.length by omega_arith, ite_true]
      rw [List.getElem_append_left (by simp [hl]; omega_arith), List.getElem_append_right (by simp [hl]; omega_arith)]
      simp only [List.length_take, hl, List.getD_eq_getElem?_getD, Nat.min_eq_left (show o ≤ n by omega_arith),
        List.getElem?_eq_getElem (show i - o < xs.length by omega_arith), Option.getD_some]
    · simp only [show ¬ (i - o < xs.length) by omega_arith, ite_false]
      rw [List.getElem_append_right (by simp [hl]; omega_arith), List.getElem_drop]
      simp only [List.length_append, List.length_take, hl, Nat.min_eq_left (show o ≤ n by omega_arith)]
      rw [getElem_bytesAt _ _ (by omega_arith), show o + xs.length + (i - (o + xs.length)) = i by omega_arith]

/-- A byte write is a write of one byte. -/
theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_cons, List.length_nil, Nat.zero_add]
  split
  · rename_i h
    simp only [show (x - a).toNat = 0 by omega_arith, List.getD_cons_zero]
    simp
  · rfl

/-- A word write is a write of its bytes, least significant first. -/
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

theorem bytesAt_writeW32_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 32) (h : o + 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le4 v ++ (bytesAt m p n).drop (o + 4) := by
  rw [writeW32_eq, bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le4]; exact h) hn, Proof.Cmac.length_le4]

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := bytesAt_writeBytes_at m p (o := 0) xs (by omega_arith) hn
  simpa using this

theorem bytesAt_writeW32_base (m : Mem) (p : Addr) {n : Nat} (v : BitVec 32) (h : 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p v) p n = le4 v ++ (bytesAt m p n).drop 4 := by
  have := bytesAt_writeW32_at m p (o := 0) v h hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

theorem bytesAt_prefix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m p a = (bytesAt m p n).take a := by
  rw [show n = a + (n - a) by omega_arith, Proof.Cmac.Stream.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

theorem bytesAt_suffix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m (p + BitVec.ofNat 64 a) (n - a) = (bytesAt m p n).drop a := by
  conv => rhs; rw [show n = a + (n - a) by omega_arith, Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_left' (length_bytesAt _ _ _)]

/-! ## Big-endian strings -/

theorem be_zero (k : Nat) : Spec.Ccm.be k 0 = Spec.Ccm.zeros k := by
  simp [Spec.Ccm.be, Spec.Ccm.zeros, List.map_const']

/-- `[v]₈ₖ` for `v < 2^(8q)` and `k ≥ q`: zeros, then `[v]₈q`. -/
theorem be_split {q k v : Nat} (hqk : q ≤ k) (hv : v < 256 ^ q) :
    Spec.Ccm.be k v = Spec.Ccm.zeros (k - q) ++ Spec.Ccm.be q v := by
  induction k with
  | zero => rw [show q = 0 by omega_arith]; simp [Spec.Ccm.zeros, Spec.Ccm.be]
  | succ k ih =>
    rcases Nat.lt_or_ge k q with h | h
    · rw [show q = k + 1 by omega_arith]; simp [Spec.Ccm.zeros]
    · rw [be_succ, ih h, show k + 1 - q = (k - q) + 1 by omega_arith, Spec.Ccm.zeros, Spec.Ccm.zeros,
        List.replicate_succ, List.cons_append]
      congr 1
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h))]
      rfl

/-- The last `k` bytes of `[v]₈q`, for `k ≤ q` and `v < 2^(8k)`, are `[v]₈ₖ`. -/
theorem be_drop {q k v : Nat} (hkq : k ≤ q) (hv : v < 256 ^ k) :
    (Spec.Ccm.be q v).drop (q - k) = Spec.Ccm.be k v := by
  rw [be_split hkq hv, List.drop_left' (by simp [Spec.Ccm.zeros])]

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

theorem le4_or (a b : BitVec 32) : le4 (a ||| b) = List.zipWith (· ||| ·) (le4 a) (le4 b) := by
  apply List.ext_getElem (by simp [le4])
  intro k h₁ h₂
  simp only [le4, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

/-- The last 4 bytes of `Ctrᵢ`: those of the nonce after its first 11, then
the last `min q 4` bytes of `[i]₈q`. -/
theorem ctrBlock_drop12 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ min (15 - nonce.length) 4) :
    (Spec.Ccm.ctrBlock nonce i).drop 12 =
      nonce.drop 11 ++ Spec.Ccm.be (min (15 - nonce.length) 4) i := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.drop_succ_cons]
  by_cases h11 : 11 ≤ nonce.length
  · rw [List.drop_append_of_le_length h11, Nat.min_eq_left (by omega_arith)]
  · rw [List.drop_append, List.drop_eq_nil_of_le (show nonce.length ≤ 11 by omega_arith), List.nil_append,
      show 11 - nonce.length = (15 - nonce.length) - min (15 - nonce.length) 4 by omega_arith,
      be_drop (by omega_arith) hi, List.nil_append]

theorem length_ctrBlock' {nonce : List Byte} (h13 : nonce.length ≤ 13) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).length = 16 := by
  simp only [Spec.Ccm.ctrBlock, List.length_cons, List.length_append, length_be]; omega_arith

/-- `Ctrᵢ`, for `i < 2³²` (and `i < 2^(8q)`), from `Ctr₀`: its first 12 bytes, and
its last 4 ORed with `[i]₃₂`. -/
theorem ctrBlock_split {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ min (15 - nonce.length) 4) :
    Spec.Ccm.ctrBlock nonce i = (Spec.Ccm.ctrBlock nonce 0).take 12 ++
      List.zipWith (· ||| ·) ((Spec.Ccm.ctrBlock nonce 0).drop 12) (Spec.Ccm.be 4 i) := by
  have hi4 : i < 256 ^ 4 := Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega_arith))
  have k0 : (0 : Nat) < 256 ^ min (15 - nonce.length) 4 := Nat.pow_pos (by decide)
  conv => lhs; rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce i)]
  congr 1
  · simp only [Spec.Ccm.ctrBlock, List.cons_append, List.take_succ_cons]
    congr 1
    by_cases h11 : 11 ≤ nonce.length
    · rw [List.take_append_of_le_length h11, List.take_append_of_le_length h11]
    · rw [List.take_append, List.take_append, be_split (q := 4) (by omega_arith) hi4,
        be_split (q := 4) (by omega_arith) (show 0 < 256 ^ 4 by decide)]
      congr 1
      rw [List.take_left' (by simp [Spec.Ccm.zeros]; omega_arith), List.take_left' (by simp [Spec.Ccm.zeros]; omega_arith)]
  · rw [ctrBlock_drop12 h7 h13 hi, ctrBlock_drop12 h7 h13 k0, be_zero,
      be_split (k := 4) (q := min (15 - nonce.length) 4) (by omega_arith) hi,
      List.zipWith_append (by simp [Spec.Ccm.zeros]; omega_arith), zipWith_or_zeros_right _ (by simp; omega_arith),
      zipWith_or_zeros_left _ (length_be _ _)]

/-- The cipher of a key schedule that a write misses. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega_arith)]

end VG.Proof.AesCcm
