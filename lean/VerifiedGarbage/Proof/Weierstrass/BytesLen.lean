import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# Short Weierstrass curves: numbers of `len` bytes in `n` words

For a curve whose encodings are not whole words (P-521's 66 bytes in nine
words), the facts the code moving them needs: a top word of `t < 8` bytes
is the first eight bytes' reversal shifted right by `8 (8 - t)` bits
(`top_bytes`), so the words, the others byte-reversed as for whole words,
are the `len` bytes big-endian (`wordsVal_eq_ofBytes_len`); a number shifted
right in place, a word at a time, from the shifted words and the low bits
of the next ones rotated to the top (`wordsVal_shr`); and the bytes of a
number written a word at a time, and its top word a byte at a time
(`bytesAt_eq_toBytes_len`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Proof.Mont
open VG.Spec.Ecdsa (bytesAt)

theorem ofBytes_singleton (x : Byte) : Spec.Weierstrass.ofBytes [x] = x.toNat := by
  show 256 * 0 + x.toNat = x.toNat
  rw [Nat.mul_zero, Nat.zero_add]

theorem ofBytes_lt (l : List Byte) : Spec.Weierstrass.ofBytes l < 256 ^ l.length := by
  induction l with
  | nil => decide
  | cons x l ih =>
    rw [show x :: l = [x] ++ l from rfl, ofBytes_append, ofBytes_singleton, List.length_append,
      List.length_singleton, Nat.pow_add, Nat.pow_one]
    have h1 : (x.toNat + 1) * 256 ^ l.length ≤ 256 * 256 ^ l.length :=
      Nat.mul_le_mul_right _ (show x.toNat + 1 ≤ 256 from x.isLt)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

theorem pow256 (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [Nat.pow_mul]

/-- A number of `n` bytes is below `2^(8 n)`. -/
theorem ofBytes_bytesAt_lt (m : Mem) (p : Addr) (n : Nat) :
    Spec.Weierstrass.ofBytes (bytesAt m p n) < 2 ^ (8 * n) := by
  have := ofBytes_lt (bytesAt m p n)
  rwa [show (bytesAt m p n).length = n by simp [bytesAt], pow256] at this

/-- The first `t ≤ 8` of eight bytes: their reversal shifted right. -/
theorem top_bytes (m : Mem) (p : Addr) {t : Nat} (ht : t ≤ 8) :
    (byteRev64 (m.readW p 64)).toNat >>> (8 * (8 - t)) = Spec.Weierstrass.ofBytes (bytesAt m p t) := by
  have e := bytesAt_add m p t (8 - t)
  rw [show t + (8 - t) = 8 by omega] at e
  have hb := ofBytes_lt (bytesAt m (p + BitVec.ofNat 64 t) (8 - t))
  rw [length_bytesAt] at hb
  rw [byteRev64_ofBytes, e, ofBytes_append, length_bytesAt, Nat.shiftRight_eq_div_pow, ← pow256,
    Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_ne_zero (by simp)), Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The words of a number of `len` bytes at `p`, `8 k < len ≤ 8 (k + 1)`: word
`j` the byte reversal of the word at `p + len - 8 (j + 1)`, or, for a top word
of fewer than eight bytes, the reversal of the first eight shifted right. -/
theorem wordsVal_eq_ofBytes_len (m m' : Mem) (base p : Addr) (o k len : Nat) (hlo : 8 * k < len)
    (hhi : len ≤ 8 * (k + 1))
    (h : ∀ j < k + 1, word m base (o + 8 * j) =
      if 8 * (j + 1) ≤ len then byteRev64 (m'.readW (p + BitVec.ofNat 64 (len - 8 * (j + 1))) 64)
      else byteRev64 (m'.readW p 64) >>> (8 * (8 * (j + 1) - len))) :
    wordsVal m base o (k + 1) = Spec.Weierstrass.ofBytes (bytesAt m' p len) := by
  have hlow := wordsVal_eq_ofBytes m m' base (p + BitVec.ofNat 64 (len - 8 * k)) o k fun j hj => by
    rw [h j (by omega), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Offset.add_add,
      show len - 8 * k + 8 * (k - 1 - j) = len - 8 * (j + 1) by omega]
  have htop : (word m base (o + 8 * k)).toNat =
      Spec.Weierstrass.ofBytes (bytesAt m' p (len - 8 * k)) := by
    rw [h k (by omega)]
    by_cases hc : 8 * (k + 1) ≤ len
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), show len - 8 * (k + 1) = 0 by omega,
        show len - 8 * k = 8 by omega, BitVec.add_zero, byteRev64_ofBytes]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), BitVec.toNat_ushiftRight,
        show 8 * (8 * (k + 1) - len) = 8 * (8 - (len - 8 * k)) by omega, top_bytes _ _ (by omega)]
  have e := bytesAt_add m' p (len - 8 * k) (8 * k)
  rw [show len - 8 * k + 8 * k = len by omega] at e
  rw [wordsVal_succ_top, hlow, htop, e, ofBytes_append, length_bytesAt, pow256,
    show 8 * (8 * k) = 64 * k by omega, Nat.mul_comm (2 ^ (64 * k)), Nat.add_comm]

/-! ## Shifting right in place -/

theorem testBit_high {x k i : Nat} (hx : x < 2 ^ k) (hi : k ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

/-- A number shifted right by `0 < sh < 64`, a word at a time: word `j` is
word `j` shifted, or'd with the low `sh` bits of word `j + 1` rotated to the
top. -/
theorem wordsVal_shr (m m' : Mem) (base : Addr) (o n sh : Nat) (hsh : 0 < sh) (hsh' : sh < 64)
    (h : ∀ j < n, word m' base (o + 8 * j) =
      if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
        (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
      else word m base (o + 8 * j) >>> sh) :
    wordsVal m' base o n = wordsVal m base o n >>> sh := by
  have hx := wordsVal_lt m base o n
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_shiftRight]
  by_cases hi : i < 64 * n
  · have hj : i / 64 < n := by omega
    have hb : i % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [show i = 64 * (i / 64) + i % 64 by omega, testBit_wordsVal _ _ _ _ _ _ hj hb, BitVec.testBit_toNat,
      h _ hj]
    by_cases hlo : sh + i % 64 < 64
    · rw [show sh + (64 * (i / 64) + i % 64) = 64 * (i / 64) + (sh + i % 64) by omega,
        testBit_wordsVal _ _ _ _ _ _ hj hlo, BitVec.testBit_toNat]
      split
      · simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
          Nat.mod_eq_of_lt hsh', show i % 64 < 64 - sh by omega, ite_true]
        simp only [show ¬sh + i % 64 < sh by omega, decide_false, Bool.and_false, Bool.or_false]
      · rw [BitVec.getLsbD_ushiftRight]
    · split
      · rename_i hn
        rw [show sh + (64 * (i / 64) + i % 64) = 64 * (i / 64 + 1) + (sh + i % 64 - 64) by omega,
          testBit_wordsVal _ _ _ _ _ _ hn (by omega), BitVec.testBit_toNat]
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
          BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
          Nat.mod_eq_of_lt hsh', show ¬i % 64 < 64 - sh by omega, ite_false, hb, decide_true,
          Bool.true_and, show i % 64 - (64 - sh) = sh + i % 64 - 64 by omega]
        rw [BitVec.getLsbD_of_ge _ _ (show 64 ≤ sh + i % 64 by omega)]
        simp only [Bool.false_or, show sh + i % 64 - 64 < 64 by omega, show sh + i % 64 - 64 < sh by omega,
          decide_true, Bool.and_true]
      · rename_i hn
        rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge _ _ (by omega),
          testBit_high hx (by omega)]
  · rw [testBit_high (wordsVal_lt m' base o n) (by omega), testBit_high hx (by omega)]

/-! ## Writing `len` bytes -/

/-- The top word of a number of `k + 1` words is it shifted right by `64 k`. -/
theorem wordsVal_shiftRight_top (m : Mem) (base : Addr) (a k : Nat) :
    wordsVal m base a (k + 1) >>> (64 * k) = (word m base (a + 8 * k)).toNat := by
  rw [wordsVal_succ_top, Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wordsVal_lt m base a k), Nat.add_zero]

/-- The `len` bytes at `q`, `8 k < len ≤ 8 (k + 1)`: words `j` (whole) the
byte reversal of the masked word `j` of a number of `k + 1` words, at
`q + len - 8 (j + 1)`, and the bytes of a top word of fewer than eight bytes
the masked word shifted right; they are the number big-endian, or zeros. -/
theorem bytesAt_eq_toBytes_len (m m₀ : Mem) (base q : Addr) {a k len : Nat} (c : Bool) (hlo : 8 * k < len)
    (hhi : len ≤ 8 * (k + 1))
    (hw : ∀ j < k + 1, 8 * (j + 1) ≤ len → m.readW (q + BitVec.ofNat 64 (len - 8 * (j + 1))) 64 =
      byteRev64 (word m₀ base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0)))
    (ht : len < 8 * (k + 1) → ∀ i < len - 8 * k, m (q + BitVec.ofNat 64 i) =
      BitVec.ofNat 8 ((word m₀ base (a + 8 * k) &&& (if c then BitVec.allOnes 64 else 0)).toNat >>>
        (8 * (len - 8 * k - 1 - i)))) :
    bytesAt m q len =
      if c then Spec.Weierstrass.toBytes len (wordsVal m₀ base a (k + 1)) else List.replicate len 0 := by
  have hb : ∀ i < len, m (q + BitVec.ofNat 64 i) =
      BitVec.ofNat 8 ((if c then wordsVal m₀ base a (k + 1) else 0) >>> (8 * (len - 1 - i))) := by
    intro i hi
    by_cases hk : i < len - 8 * k ∧ len < 8 * (k + 1)
    · rw [ht hk.2 i hk.1]
      refine congrArg (BitVec.ofNat 8) ?_
      cases c
      · simp
      · simp only [ite_true, BitVec.and_allOnes]
        rw [← wordsVal_shiftRight_top, ← Nat.shiftRight_add,
          show 64 * k + 8 * (len - 8 * k - 1 - i) = 8 * (len - 1 - i) by omega]
    · have hj : (len - 1 - i) / 8 < k + 1 := by omega
      have hj8 : 8 * ((len - 1 - i) / 8 + 1) ≤ len := by omega
      have e := byte_word m (q + BitVec.ofNat 64 (len - 8 * ((len - 1 - i) / 8 + 1))) 0
        (r := i - (len - 8 * ((len - 1 - i) / 8 + 1))) (by omega)
      rw [Nat.mul_zero, Nat.zero_add, show q + BitVec.ofNat 64 (len - 8 * ((len - 1 - i) / 8 + 1)) +
          BitVec.ofNat 64 0 = q + BitVec.ofNat 64 (len - 8 * ((len - 1 - i) / 8 + 1)) from BitVec.add_zero _,
        Offset.add_add_eq q (show len - 8 * ((len - 1 - i) / 8 + 1) + (i - (len - 8 * ((len - 1 - i) / 8 + 1))) = i
          by omega), hw _ hj hj8] at e
      rw [e]
      apply BitVec.eq_of_getLsbD_eq
      intro b hb
      rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, decide_eq_true hb, Bool.true_and, Bool.true_and,
        getLsbD_byteRev64 _ (by omega), BitVec.getLsbD_and]
      cases c
      · simp
      · simp only [ite_true, BitVec.getLsbD_allOnes]
        rw [decide_eq_true (by omega), Bool.and_true, Nat.testBit_shiftRight,
          show 8 * (len - 1 - i) + b = 64 * ((len - 1 - i) / 8) +
            (8 * (7 - (8 * (i - (len - 8 * ((len - 1 - i) / 8 + 1))) + b) / 8) +
              (8 * (i - (len - 8 * ((len - 1 - i) / 8 + 1))) + b) % 8) by omega,
          testBit_wordsVal _ _ _ _ _ _ hj (by omega), BitVec.testBit_toNat]
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
