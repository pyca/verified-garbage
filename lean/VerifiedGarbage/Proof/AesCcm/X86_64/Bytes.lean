import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# AES-CCM on x86-64: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean. A write of a byte, a word or
bytes into a buffer replaces those of its bytes (`bytesAt_writeBytes_at`,
`bytesAt_writeW8_at`, `bytesAt_writeW64_at`, `bytesAt_writeW32_at`): the
pieces build their blocks (`Ctr₀`, `B₀`, the first block of the associated
data, a last block padded) as lists.
-/

set_option linter.unusedSimpArgs false

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

/-! ## Words as bytes -/

theorem le8_or (a b : BitVec 64) : le8 (a ||| b) = List.zipWith (· ||| ·) (le8 a) (le8 b) := by
  apply List.ext_getElem (by simp [le8])
  intro k h₁ h₂
  simp only [le8, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

theorem bswap64_bytes (x : BitVec 64) :
    (List.range 8).map (fun j => (bswap64 x).extractLsb' (8 * j) 8) =
      (List.range 8).reverse.map (fun i => x.extractLsb' (8 * i) 8) := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.reverse_cons, List.reverse_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp (disch := decide) only [bswap64, Nat.mul_zero, Nat.reduceMul, extractLsb'_append_byte_lo,
      extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

theorem le8_bswap64 (x : BitVec 64) : le8 (bswap64 x) = (le8 x).reverse := by
  simp only [le8]
  rw [bswap64_bytes, List.map_reverse]

/-- The bytes of `[v]₆₄`, the most significant first. -/
theorem le8_bswap64_ofNat {v : Nat} (hv : v < 2 ^ 64) : le8 (bswap64 (BitVec.ofNat 64 v)) = Spec.Ccm.be 8 v := by
  rw [le8_bswap64]
  apply List.ext_getElem (by simp [le8, Proof.AesCcm.length_be])
  intro k h₁ h₂
  have hk : k < 8 := by simpa [le8] using h₁
  simp only [List.getElem_reverse, le8, List.getElem_map, List.getElem_range, List.length_map,
    List.length_range, Spec.Ccm.be]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hv, show 8 - 1 - k = 7 - k by omega, show 2 ^ (8 * (7 - k)) = 256 ^ (7 - k) by
    rw [Nat.pow_mul]]

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
    · rw [Proof.AesCcm.be_succ, ih h, show k + 1 - q = (k - q) + 1 by omega, Spec.Ccm.zeros, Spec.Ccm.zeros,
        List.replicate_succ, List.cons_append]
      congr 1
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h))]
      rfl

/-- The last 8 bytes of `Ctrᵢ`: the nonce's bytes after its first 7, then `[i]₈q`. -/
theorem ctrBlock_drop8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).drop 8 = nonce.drop 7 ++ Spec.Ccm.be (15 - nonce.length) i := by
  simp [Spec.Ccm.ctrBlock, List.drop_append_of_le_length (show 7 ≤ nonce.length from h7)]

theorem ctrBlock_take8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).take 8 = BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
  simp [Spec.Ccm.ctrBlock, List.take_append_of_le_length (show 7 ≤ nonce.length from h7)]

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

/-- `Ctrᵢ`'s last 8 bytes, from `Ctr₀`'s and `[i]₆₄`. -/
theorem ctr_or {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w : BitVec 64}
    (hw : le8 w = (Spec.Ccm.ctrBlock nonce 0).drop 8) {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) :
    le8 (bswap64 (BitVec.ofNat 64 i) ||| w) = (Spec.Ccm.ctrBlock nonce i).drop 8 := by
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi (by
    rw [show 2 ^ 64 = 256 ^ 8 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega))
  rw [le8_or, le8_bswap64_ofNat hi64, hw, ctrBlock_drop8 h7, ctrBlock_drop8 h7, be_zero,
    be_split (q := 15 - nonce.length) (by omega) hi,
    List.zipWith_comm_of_comm (f := (· ||| ·)) (fun a b => BitVec.or_comm a b)]
  have hd : (nonce.drop 7).length = 8 - (15 - nonce.length) := by rw [List.length_drop]; omega
  rw [List.zipWith_append (by rw [hd]; simp [Spec.Ccm.zeros]), zipWith_or_zeros_right _ hd,
    zipWith_or_zeros_left _ (Proof.AesCcm.length_be _ _)]

end VG.Proof.AesCcm.X86_64
