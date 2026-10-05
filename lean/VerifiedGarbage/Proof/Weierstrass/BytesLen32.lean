import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.BytesLen

/-!
# Short Weierstrass curves: numbers of `len` bytes in 32-bit words

For the targets with 32-bit registers, what `Proof/Weierstrass/BytesLen.lean`
says of 64-bit words, for a curve whose encodings are not whole words
(P-521's 66 bytes in the eighteen 32-bit words of nine 64-bit ones): a word
of `t < 4` bytes is the first four bytes' reversal shifted right by
`8 (4 - t)` bits (`top_bytes32`), so the words, the whole ones byte-reversed
and those past `len` zero, are the `len` bytes big-endian
(`val32_eq_ofBytes_len`); a number shifted right in place, a word at a time
(`val32_shr`); and the bytes of a number written a word at a time, and a
word of fewer bytes a byte at a time (`bytesAt_eq_toBytes_len32`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Proof.Mont
open VG.Spec.Ecdsa (bytesAt)

/-- The first `t ≤ 4` of four bytes: their reversal shifted right. -/
theorem top_bytes32 (m : Mem) (p : Addr) {t : Nat} (ht : t ≤ 4) :
    (byteRev32 (m.readW p 32)).toNat >>> (8 * (4 - t)) = Spec.Weierstrass.ofBytes (bytesAt m p t) := by
  have e := bytesAt_add m p t (4 - t)
  rw [show t + (4 - t) = 4 by omega] at e
  have hb := ofBytes_lt (bytesAt m (p + BitVec.ofNat 64 t) (4 - t))
  rw [length_bytesAt] at hb
  rw [byteRev32_ofBytes, e, ofBytes_append, length_bytesAt, Nat.shiftRight_eq_div_pow, ← pow256,
    Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by simp)), Nat.div_eq_of_lt hb, Nat.add_zero]

/-- Word `j` of a number of `len` bytes at `p`: the byte reversal of the word
at `p + len - 4 (j + 1)`, for a word of fewer bytes the reversal of the
first four shifted right, and zero past `len`. -/
def ldWord32 (m : Mem) (p : Addr) (len j : Nat) : Nat :=
  if 4 * (j + 1) ≤ len then (byteRev32 (m.readW (p + BitVec.ofNat 64 (len - 4 * (j + 1))) 32)).toNat
  else if 4 * j < len then (byteRev32 (m.readW p 32)).toNat >>> (8 * (4 * (j + 1) - len))
  else 0

/-- The words `ldWord32` of `len ≤ 4 N` bytes at `p` are the bytes
big-endian. -/
theorem val32_eq_ofBytes_len (m m' : Mem) (base p : Addr) (o N len : Nat) (h4 : 4 ≤ len) (hN : len ≤ 4 * N)
    (h : ∀ j < N, w32 m base (o + 4 * j) = ldWord32 m' p len j) :
    val32 m base o N = Spec.Weierstrass.ofBytes (bytesAt m' p len) := by
  obtain ⟨k, hk⟩ : ∃ k, k = (len - 1) / 4 := ⟨_, rfl⟩
  have hk1 : 4 * k < len := by omega
  have hk2 : len ≤ 4 * (k + 1) := by omega
  rw [show N = (k + 1) + (N - (k + 1)) by omega, val32_append]
  have hz : val32 m base (o + 4 * (k + 1)) (N - (k + 1)) = 0 := (val32_eq_zero_iff _ _ _ _).mpr fun j hj => by
    rw [show o + 4 * (k + 1) + 4 * j = o + 4 * (k + 1 + j) by omega, h _ (by omega), ldWord32,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rw [hz, Nat.mul_zero, Nat.add_zero, val32_succ]
  have hlow := val32_eq_ofBytes m m' base (p + BitVec.ofNat 64 (len - 4 * k)) o k fun j hj => by
    rw [h j (by omega), ldWord32, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Offset.add_add,
      show len - 4 * k + 4 * (k - 1 - j) = len - 4 * (j + 1) by omega]
  have htop : w32 m base (o + 4 * k) = Spec.Weierstrass.ofBytes (bytesAt m' p (len - 4 * k)) := by
    rw [h k (by omega), ldWord32]
    by_cases hc : 4 * (k + 1) ≤ len
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), show len - 4 * (k + 1) = 0 by omega,
        show len - 4 * k = 4 by omega, BitVec.add_zero, byteRev32_ofBytes]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_left_of_eq_true _ _ (eq_true hk1),
        show 8 * (4 * (k + 1) - len) = 8 * (4 - (len - 4 * k)) by omega, top_bytes32 _ _ (by omega)]
  have e := bytesAt_add m' p (len - 4 * k) (4 * k)
  rw [show len - 4 * k + 4 * k = len by omega] at e
  rw [hlow, htop, e, ofBytes_append, length_bytesAt, pow256, show 8 * (4 * k) = 32 * k by omega,
    Nat.mul_comm (2 ^ (32 * k)), Nat.add_comm]

/-! ## Shifting right in place -/

/-- A number of `N` 32-bit words shifted right by `0 < sh < 32`, a word at a
time: word `j` is word `j` shifted, or'd with the low `sh` bits of word
`j + 1` rotated to the top. -/
theorem val32_shr (m m' : Mem) (base : Addr) (o N sh : Nat) (hsh : 0 < sh) (hsh' : sh < 32)
    (h : ∀ j < N, m'.readW (off base (o + 4 * j)) 32 =
      if j + 1 < N then (m.readW (off base (o + 4 * j)) 32 >>> sh) |||
        (m.readW (off base (o + 4 * (j + 1))) 32 &&& BitVec.ofNat 32 (2 ^ sh - 1)).rotateRight sh
      else m.readW (off base (o + 4 * j)) 32 >>> sh) :
    val32 m' base o N = val32 m base o N >>> sh := by
  have hx := val32_lt m base o N
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_shiftRight]
  by_cases hi : i < 32 * N
  · have hj : i / 32 < N := by omega
    have hb : i % 32 < 32 := Nat.mod_lt _ (by decide)
    rw [show i = 32 * (i / 32) + i % 32 by omega, testBit_val32 _ _ _ _ _ _ hj hb, BitVec.testBit_toNat,
      h _ hj]
    by_cases hlo : sh + i % 32 < 32
    · rw [show sh + (32 * (i / 32) + i % 32) = 32 * (i / 32) + (sh + i % 32) by omega,
        testBit_val32 _ _ _ _ _ _ hj hlo, BitVec.testBit_toNat]
      split
      · simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
          Nat.mod_eq_of_lt hsh', show i % 32 < 32 - sh by omega, ite_true]
        simp only [show ¬sh + i % 32 < sh by omega, decide_false, Bool.and_false, Bool.or_false]
      · rw [BitVec.getLsbD_ushiftRight]
    · split
      · rename_i hn
        rw [show sh + (32 * (i / 32) + i % 32) = 32 * (i / 32 + 1) + (sh + i % 32 - 32) by omega,
          testBit_val32 _ _ _ _ _ _ hn (by omega), BitVec.testBit_toNat]
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
          Nat.mod_eq_of_lt hsh', show ¬i % 32 < 32 - sh by omega, ite_false, hb, decide_true,
          Bool.true_and, show i % 32 - (32 - sh) = sh + i % 32 - 32 by omega]
        rw [BitVec.getLsbD_of_ge _ _ (show 32 ≤ sh + i % 32 by omega)]
        simp only [Bool.false_or, show sh + i % 32 - 32 < 32 by omega, show sh + i % 32 - 32 < sh by omega,
          decide_true, Bool.and_true]
      · rename_i hn
        rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega),
          testBit_high hx (by omega)]
  · rw [testBit_high (val32_lt m' base o N) (by omega), testBit_high hx (by omega)]

/-! ## Writing `len` bytes -/

/-- The `len` bytes at `q` (`len ≤ 4 N`): the words `j` with
`4 (j + 1) ≤ len` the byte reversal of the masked word `j` of a number of
`N` words, at `q + len - 4 (j + 1)`, and the bytes of a word of fewer bytes
the masked word shifted right; they are the number big-endian, or zeros. -/
theorem bytesAt_eq_toBytes_len32 (m m₀ : Mem) (base q : Addr) {a N len : Nat} (c : Bool) (hN : len ≤ 4 * N)
    (hw : ∀ j < N, 4 * (j + 1) ≤ len → m.readW (q + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
      byteRev32 (m₀.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0)))
    (ht : ∀ k < N, 4 * k < len → len < 4 * (k + 1) → ∀ i < len - 4 * k, m (q + BitVec.ofNat 64 i) =
      BitVec.ofNat 8 ((m₀.readW (off base (a + 4 * k)) 32 &&& (if c then BitVec.allOnes 32 else 0)).toNat >>>
        (8 * (len - 4 * k - 1 - i)))) :
    bytesAt m q len =
      if c then Spec.Weierstrass.toBytes len (val32 m₀ base a N) else List.replicate len 0 := by
  have hb : ∀ i < len, m (q + BitVec.ofNat 64 i) =
      BitVec.ofNat 8 ((if c then val32 m₀ base a N else 0) >>> (8 * (len - 1 - i))) := by
    intro i hi
    have hj : (len - 1 - i) / 4 < N := by omega
    by_cases hk : 4 * ((len - 1 - i) / 4 + 1) ≤ len
    · have e := byte_word32 m (q + BitVec.ofNat 64 (len - 4 * ((len - 1 - i) / 4 + 1))) 0
        (r := i - (len - 4 * ((len - 1 - i) / 4 + 1))) (by omega)
      rw [Nat.mul_zero, Nat.zero_add, show q + BitVec.ofNat 64 (len - 4 * ((len - 1 - i) / 4 + 1)) +
          BitVec.ofNat 64 0 = q + BitVec.ofNat 64 (len - 4 * ((len - 1 - i) / 4 + 1)) from BitVec.add_zero _,
        Offset.add_add_eq q (show len - 4 * ((len - 1 - i) / 4 + 1) + (i - (len - 4 * ((len - 1 - i) / 4 + 1))) = i
          by omega), hw _ hj hk] at e
      rw [e]
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, decide_eq_true hb, Bool.true_and, Bool.true_and,
        getLsbD_byteRev32 _ (by omega), BitVec.getLsbD_and]
      cases c
      · simp
      · simp only [ite_true, BitVec.getLsbD_allOnes]
        rw [decide_eq_true (by omega), Bool.and_true, Nat.testBit_shiftRight,
          show 8 * (len - 1 - i) + b = 32 * ((len - 1 - i) / 4) +
            (8 * (3 - (8 * (i - (len - 4 * ((len - 1 - i) / 4 + 1))) + b) / 8) +
              (8 * (i - (len - 4 * ((len - 1 - i) / 4 + 1))) + b) % 8) by omega,
          testBit_val32 _ _ _ _ _ _ hj (by omega), BitVec.testBit_toNat]
    · rw [ht _ hj (by omega) (by omega) i (by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro b hb8
      simp only [BitVec.getLsbD_ofNat, decide_eq_true hb8, Bool.true_and, Nat.testBit_shiftRight]
      cases c
      · simp
      · simp only [ite_true, BitVec.and_allOnes, BitVec.testBit_toNat]
        rw [show 8 * (len - 1 - i) + b = 32 * ((len - 1 - i) / 4) +
            (8 * (len - 4 * ((len - 1 - i) / 4) - 1 - i) + b) by omega,
          testBit_val32 _ _ _ _ _ _ hj (by omega), BitVec.testBit_toNat]
  cases c
  · simp only [Bool.false_eq_true, ite_false] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, List.length_replicate]) fun i h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, List.getElem_replicate, hb i h₁, Nat.zero_shiftRight]
    rfl
  · simp only [ite_true] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, length_toBytes]) fun i h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, getElem_toBytes, hb i h₁]

end VG.Proof.Weierstrass
