import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.Words32

/-!
# Short Weierstrass curves: numbers as 32-bit words and bytes

For the targets with 32-bit registers, what `Proof/Weierstrass/Words.lean`
says of 64-bit words: the bits of a number of 32-bit words (`val32`), and its
big-endian encodings through byte-reversed words (`val32_eq_ofBytes`,
`bytesAt_eq_toBytes32`).
-/

namespace VG.Proof.Weierstrass

open VG VG.Proof.Mont
open VG.Spec.Ecdsa (bytesAt)

/-- Bit `32 j + b` of a number is bit `b` of its word `j`. -/
theorem testBit_val32 (m : Mem) (base : Addr) : ∀ (a n j b : Nat), j < n → b < 32 →
    (val32 m base a n).testBit (32 * j + b) = (w32 m base (a + 4 * j)).testBit b
  | _, 0, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | a, n + 1, j, b, hj, hb => by
    rw [val32, Nat.add_comm (w32 m base a), Nat.testBit_two_pow_mul_add _ (m.readW (off base a) 32).isLt]
    rcases j with _ | j
    · simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
      exact ite_eq_left hb
    · rw [ite_eq_right (show ¬32 * (j + 1) + b < 32 by omega), show 32 * (j + 1) + b - 32 = 32 * j + b by omega,
        testBit_val32 m base (a + 4) n j b (by omega) hb, show a + 4 + 4 * j = a + 4 * (j + 1) by omega]

/-- Byte `4 j + r` of memory at `p` is byte `r` of the word at `p + 4 j`. -/
theorem byte_word32 (m : Mem) (p : Addr) (j : Nat) {r : Nat} (hr : r < 4) :
    m (p + BitVec.ofNat 64 (4 * j + r)) = (m.readW (p + BitVec.ofNat 64 (4 * j)) 32).extractLsb' (8 * r) 8 := by
  rw [show (m.readW (p + BitVec.ofNat 64 (4 * j)) 32) = m.read (p + BitVec.ofNat 64 (4 * j)) 4 from rfl,
    Mem.extractLsb'_read _ _ hr, Offset.add_add]

/-- A byte-reversed word is the four bytes big-endian. -/
theorem byteRev32_ofBytes (m : Mem) (q : Addr) :
    (byteRev32 (m.readW q 32)).toNat = Spec.Weierstrass.ofBytes (bytesAt m q 4) := by
  have e2 : q + 1 + 1 = q + BitVec.ofNat 64 2 := by rw [BitVec.add_assoc]; rfl
  have e3 : q + BitVec.ofNat 64 2 + 1 = q + BitVec.ofNat 64 3 := by rw [BitVec.add_assoc]; rfl
  rw [byteRev32_readW, e2, e3,
    show bytesAt m q 4 = [m (q + BitVec.ofNat 64 0), m (q + BitVec.ofNat 64 1), m (q + BitVec.ofNat 64 2),
      m (q + BitVec.ofNat 64 3)] from rfl,
    show q + BitVec.ofNat 64 0 = q from BitVec.add_zero q,
    show q + BitVec.ofNat 64 1 = q + 1 from rfl]
  simp only [BitVec.toNat_append, shl8_or, Spec.Weierstrass.ofBytes, List.foldl_cons, List.foldl_nil]
  omega

/-- The words `j` of a number, each the byte reversal of the word at
`p + 4 (k - 1 - j)`, are the `4 k` bytes at `p` big-endian. -/
theorem val32_eq_ofBytes (m m' : Mem) (base p : Addr) : ∀ (o k : Nat),
    (∀ j < k, w32 m base (o + 4 * j) = (byteRev32 (m'.readW (p + BitVec.ofNat 64 (4 * (k - 1 - j))) 32)).toNat) →
    val32 m base o k = Spec.Weierstrass.ofBytes (bytesAt m' p (4 * k))
  | _, 0, _ => rfl
  | o, k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.add_sub_cancel, Nat.sub_zero] at h0
    rw [val32, val32_eq_ofBytes m m' base p (o + 4) k fun j hj => by
        rw [show o + 4 + 4 * j = o + 4 * (j + 1) by omega, h (j + 1) (by omega),
          show k + 1 - 1 - (j + 1) = k - 1 - j by omega],
      show 4 * (k + 1) = 4 * k + 4 by omega, bytesAt_add, ofBytes_append, length_bytesAt,
      ← byteRev32_ofBytes, ← h0, show (256 : Nat) ^ 4 = 2 ^ 32 from rfl]
    omega

/-- The bit `i < 32` of a byte-reversed word. -/
theorem getLsbD_byteRev32 (w : BitVec 32) {i : Nat} (hi : i < 32) :
    (byteRev32 w).getLsbD i = w.getLsbD (8 * (3 - i / 8) + i % 8) := by
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [byteRev32, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- The `4 n` bytes at `q`, the word `j` of each is the byte reversal of the
masked word `j` of a number, are the number big-endian, or zeros. -/
theorem bytesAt_eq_toBytes32 (m m₀ : Mem) (base q : Addr) {a n : Nat} (c : Bool)
    (h : ∀ j < n, m.readW (q + BitVec.ofNat 64 (4 * (n - 1 - j))) 32 =
      byteRev32 (m₀.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0))) :
    bytesAt m q (4 * n) =
      if c then Spec.Weierstrass.toBytes (4 * n) (val32 m₀ base a n) else List.replicate (4 * n) 0 := by
  have hb : ∀ k (hk : k < 4 * n), m (q + BitVec.ofNat 64 k) =
      (byteRev32 (m₀.readW (off base (a + 4 * (n - 1 - k / 4))) 32 &&&
        (if c then BitVec.allOnes 32 else 0))).extractLsb' (8 * (k % 4)) 8 := fun k hk => by
    have e := byte_word32 m q (k / 4) (r := k % 4) (Nat.mod_lt _ (by decide))
    rw [show 4 * (k / 4) + k % 4 = k by omega,
      show 4 * (k / 4) = 4 * (n - 1 - (n - 1 - k / 4)) by omega, h _ (by omega)] at e
    exact e
  cases c
  · simp only [Bool.false_eq_true, ite_false] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, List.length_replicate]) fun k h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, List.getElem_replicate, hb k h₁]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : 8 * (k % 4) + i < 32 := by omega
    have z : ∀ {w} j, (0 : BitVec w).getLsbD j = false := fun _ => BitVec.getLsbD_zero
    simp only [BitVec.getLsbD_extractLsb', getLsbD_byteRev32 _ this, BitVec.getLsbD_and, z, Bool.and_false]
  · simp only [ite_true, BitVec.and_allOnes] at hb ⊢
    refine List.ext_getElem (by rw [length_bytesAt, length_toBytes]) fun k h₁ _ => ?_
    rw [length_bytesAt] at h₁
    rw [getElem_bytesAt, getElem_toBytes, hb k h₁]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and, Bool.true_and,
      getLsbD_byteRev32 _ (by omega), Nat.testBit_shiftRight,
      show 8 * (4 * n - 1 - k) + i = 32 * (n - 1 - k / 4) + (8 * (3 - (8 * (k % 4) + i) / 8) + (8 * (k % 4) + i) % 8)
        by omega,
      testBit_val32 _ _ _ _ _ _ (by omega) (by omega), BitVec.testBit_toNat]

/-- A number is zero iff its words are. -/
theorem val32_eq_zero_iff (m : Mem) (base : Addr) : ∀ (a n : Nat),
    val32 m base a n = 0 ↔ ∀ j < n, w32 m base (a + 4 * j) = 0
  | _, 0 => ⟨fun _ _ hj => absurd hj (Nat.not_lt_zero _), fun _ => rfl⟩
  | a, n + 1 => by
    rw [val32]
    constructor
    · intro h j hj
      rcases j with _ | j
      · rw [Nat.mul_zero, Nat.add_zero]; omega
      · rw [show a + 4 * (j + 1) = a + 4 + 4 * j by omega]
        refine (val32_eq_zero_iff m base (a + 4) n).mp ?_ j (by omega)
        have : 2 ^ 32 * val32 m base (a + 4) n = 0 := by omega
        rcases Nat.mul_eq_zero.mp this with h' | h'
        · exact absurd h' (by decide)
        · exact h'
    · intro h
      have h0 := h 0 (by omega)
      rw [Nat.mul_zero, Nat.add_zero] at h0
      rw [h0, (val32_eq_zero_iff m base (a + 4) n).mpr fun j hj => by
        rw [show a + 4 + 4 * j = a + 4 * (j + 1) by omega]; exact h (j + 1) (by omega)]

end VG.Proof.Weierstrass
