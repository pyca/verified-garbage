import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# Bitsliced Camellia: words, bytes and blocks

The code loads a half of each block as a little-endian 64-bit word, whose
byte `i` is the half's byte `i` (from the most significant), and transposes
eight such words into planes (`toBsG`) and back (`fromBsG`). `WordRel W d`
says the words `W` hold the halves `d` that way; `half_of_words` and
`words_of_half` are the transposes. The halves of a block are bytes 0–7
and 8–15 of its big-endian number (`byteOf_hi`, `byteOf_lo`), and a block
is encoded back the same way (`encodeBlock_getElem`).
-/

namespace VG.Proof.Camellia

open VG VG.Spec.Camellia

/-- The words `W` hold the halves `d`: byte `i` of word `b` is byte `i`
(from the most significant) of `d b`. -/
def WordRel (W : Nat → BitVec 64) (d : Nat → BitVec 64) : Prop :=
  ∀ b < 8, ∀ i < 8, ∀ j < 8, (W b).getLsbD (8 * i + j) = (byteOf (d b) i).getLsbD j

theorem half_of_words {W Q : Nat → BitVec 64} {d : Nat → BitVec 64}
    (hT : ∀ j < 8, ∀ p < 64, (Q j).getLsbD p = (W (p % 8)).getLsbD (8 * pos (p / 8) + j))
    (hw : WordRel W d) : HalfRel Q d := by
  intro b hb c hc j hj
  rw [hT j hj _ (by omega), show (8 * c + b) % 8 = b by omega, show (8 * c + b) / 8 = c by omega,
    hw b hb _ (pos_lt hc) j hj]

theorem words_of_half {W Q : Nat → BitVec 64} {d : Nat → BitVec 64}
    (hF : ∀ b < 8, ∀ t < 64, (W b).getLsbD t = (Q (t % 8)).getLsbD (8 * cpos (t / 8) + b))
    (hq : HalfRel Q d) : WordRel W d := by
  intro b hb i hi j hj
  rw [hF b hb _ (by omega), show (8 * i + j) % 8 = j by omega, show (8 * i + j) / 8 = i by omega,
    hq b hb _ (cpos_lt hi) j hj, pos_cpos hi]

/-! ## Big-endian numbers -/

theorem testBit_foldl_bytes (l : List Byte) (a k : Nat) :
    (l.foldl (fun acc b => 256 * acc + b.toNat) a).testBit k =
      if k < 8 * l.length then (l.getD (l.length - 1 - k / 8) 0).getLsbD (k % 8)
      else a.testBit (k - 8 * l.length) := by
  induction l generalizing a k with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    have hstep : ∀ m, (256 * a + b.toNat).testBit m = if m < 8 then b.getLsbD m else a.testBit (m - 8) := by
      intro m
      rw [show 256 * a + b.toNat = 2 ^ 8 * a + b.toNat by rfl, Nat.testBit_two_pow_mul_add a b.isLt]
      split <;> simp [BitVec.testBit_toNat]
    by_cases h1 : k < 8 * l.length
    · simp only [h1, show k < 8 * (l.length + 1) by omega, ↓reduceIte]
      rw [show l.length + 1 - 1 - k / 8 = (l.length - 1 - k / 8) + 1 by omega, List.getD_cons_succ]
    · simp only [h1, ↓reduceIte, hstep]
      by_cases h2 : k - 8 * l.length < 8
      · simp only [h2, show k < 8 * (l.length + 1) by omega, ↓reduceIte,
          show l.length + 1 - 1 - k / 8 = 0 by omega, List.getD_cons_zero]
        congr 1; omega
      · simp only [h2, show ¬ k < 8 * (l.length + 1) by omega, ↓reduceIte]
        congr 1 <;> omega

theorem getLsbD_ofBytes (n : Nat) (l : List Byte) {k : Nat} (hk : k < n) (hl : 8 * l.length = n) :
    (ofBytes n l).getLsbD k = (l.getD (l.length - 1 - k / 8) 0).getLsbD (k % 8) := by
  rw [ofBytes, BitVec.getLsbD_ofNat, testBit_foldl_bytes]
  simp [hk, show k < 8 * l.length by omega]

/-- Byte `i` of the left half of a block is its byte `i`. -/
theorem byteOf_hi (blk : Block) {i : Nat} (hi : i < 8) :
    byteOf ((decodeBlock blk >>> 64).setWidth 64) i = blk[i] := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_byteOf _ hi hj, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, decodeBlock,
    getLsbD_ofBytes 128 _ (by omega) (by simp)]
  simp only [show 56 - 8 * i + j < 64 by omega, decide_true, Bool.true_and, Vector.length_toList]
  rw [show 16 - 1 - (64 + (56 - 8 * i + j)) / 8 = i by omega,
    show (64 + (56 - 8 * i + j)) % 8 = j by omega]
  simp [show i < 16 by omega]

/-- Byte `i` of the right half of a block is its byte `8 + i`. -/
theorem byteOf_lo (blk : Block) {i : Nat} (hi : i < 8) :
    byteOf ((decodeBlock blk).setWidth 64) i = blk[8 + i] := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_byteOf _ hi hj, BitVec.getLsbD_setWidth, decodeBlock,
    getLsbD_ofBytes 128 _ (by omega) (by simp)]
  simp only [show 56 - 8 * i + j < 64 by omega, decide_true, Bool.true_and, Vector.length_toList]
  rw [show 16 - 1 - (56 - 8 * i + j) / 8 = 8 + i by omega, show (56 - 8 * i + j) % 8 = j by omega]
  simp [show 8 + i < 16 by omega]

/-- The bytes of `hi ++ lo`: bytes 0–7 are `hi`'s, 8–15 `lo`'s. -/
theorem encodeBlock_getElem (hi lo : BitVec 64) {i : Nat} (h : i < 16) :
    (encodeBlock (hi ++ lo))[i] = if i < 8 then byteOf hi i else byteOf lo (i - 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [encodeBlock, Vector.getElem_ofFn, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases hi8 : i < 8
  · simp only [hi8, ↓reduceIte, show ¬ 8 * (15 - i) + j < 64 by omega, getLsbD_byteOf _ hi8 hj]
    congr 1; omega
  · simp only [hi8, ↓reduceIte, show 8 * (15 - i) + j < 64 by omega, getLsbD_byteOf _ (show i - 8 < 8 by omega) hj]
    congr 1; omega

end VG.Proof.Camellia
