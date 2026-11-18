module

import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Sha256.Spec
public import VerifiedGarbage.Impl.Sha256.X86_64.Avx2
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Spec

/-! ### `Sha256.X86_64.Avx2.Schedule`, which the modules that import this one used -/

section

/-!
# SHA-256 with AVX2 on x86-64: the message schedule of one lane

Each 256-bit instruction of the schedule acts on the two 128-bit lanes alike,
so it is proved once, on one lane (`xupd`): the next four words of a block's
schedule from its previous sixteen.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (Word Block W ssig0 ssig1)
open VG.Proof.Sha256.X86_64.ShaNi (quad W_ge')

/-! ## The instructions, on doublewords -/

theorem dword_xor (a b : BitVec 128) (k : Nat) : dword (a ^^^ b) k = dword a k ^^^ dword b k := by
  ext i hi
  simp only [dword, BitVec.getElem_extractLsb', BitVec.getLsbD_xor, BitVec.getElem_xor]

theorem xor_ofDwords (a b : BitVec 128) :
    a ^^^ b = ofDwords (dword a 0 ^^^ dword b 0) (dword a 1 ^^^ dword b 1) (dword a 2 ^^^ dword b 2)
      (dword a 3 ^^^ dword b 3) := by
  apply ext_dword <;> simp only [dword_xor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem psrld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrld a n =
      ofDwords (dword a 0 >>> n.toNat) (dword a 1 >>> n.toNat) (dword a 2 >>> n.toNat)
        (dword a 3 >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega_using [h], ite_false]

theorem pslld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .pslld a n =
      ofDwords (dword a 0 <<< n.toNat) (dword a 1 <<< n.toNat) (dword a 2 <<< n.toNat)
        (dword a 3 <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega_using [h], ite_false]

theorem qword_ofDwords_0 (a c b d : BitVec 32) : qword (ofDwords a c b d) 0 = c ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero,
    Nat.zero_add, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 32 < 32 by omega_using [hi], ite_true]

theorem qword_ofDwords_1 (a c b d : BitVec 32) : qword (ofDwords a c b d) 1 = d ++ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one,
    decide_eq_true hi, Bool.true_and, show ¬ 64 + i < 32 by omega_using [], show ¬ 64 + i - 32 < 32 by omega_using [],
    ite_false]
  by_cases h : i < 32
  · simp only [h, ite_true, show 64 + i - 32 - 32 = i by omega_using []]
  · simp only [h, show ¬ 64 + i - 32 - 32 < 32 by omega_using [h], ite_false,
      show 64 + i - 32 - 32 - 32 = i - 32 by omega_using []]

theorem shr_append (c a : BitVec 32) {m : Nat} (h : m < 32) :
    (c ++ a : BitVec 64) >>> m = (c >>> m) ++ (a >>> m ||| c <<< (32 - m)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · by_cases h2 : m + i < 32
    · simp only [h1, h2, ite_true, decide_true, show i < 32 - m by omega_using [h2], Bool.not_true, Bool.true_and,
        Bool.false_and, Bool.or_false]
    · simp only [h1, h2, ite_true, ite_false, decide_true, show ¬ i < 32 - m by omega_using [h2], decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge a (m + i) (by omega_using [h2]), Bool.false_or,
        show i - (32 - m) = m + i - 32 by omega_using [h]]
  · simp only [h1, show ¬ m + i < 32 by omega_using [h1], ite_false, show m + (i - 32) = m + i - 32 by omega_using [h1]]

theorem append_pairs (p q r s : BitVec 32) : (p ++ q) ++ (r ++ s) = ofDwords s r q p := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ofDwords, BitVec.getLsbD_append]
  simp only [Nat.reduceAdd, Nat.sub_sub]
  by_cases h1 : i < 32
  · simp only [h1, show i < 64 by omega_using [h1], ite_true]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega_using [h2], ite_true, ite_false]
  by_cases h3 : i < 96
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega_using [h2], show i - 64 < 32 by omega_using [h3], ite_true, ite_false]
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega_using [h2], show ¬ i - 64 < 32 by omega_using [h3], ite_false]

/-- A quadword shift right, on doublewords: the high doubleword of each
quadword shifts into the low one. -/
theorem psrlq_eq (a c b d : BitVec 32) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrlq (ofDwords a c b d) n =
      ofDwords (a >>> n.toNat ||| c <<< (32 - n.toNat)) (c >>> n.toNat)
        (b >>> n.toNat ||| d <<< (32 - n.toNat)) (d >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega_using [h], ite_false, qword_ofDwords_0,
    qword_ofDwords_1, shr_append _ _ h, append_pairs]

theorem pshufb_BA_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a maskBA =
      ofBytes fun j => if j < 4 then byte a j else if j < 8 then byte a (j + 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_DC_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a maskDC =
      ofBytes fun j => if j < 8 then 0 else if j < 12 then byte a (j - 8) else byte a (j - 4) := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- `vpshufb` with `maskBA`: doublewords 0 and 2 into 0 and 1, zeros above. -/
theorem pshufb_BA (a : BitVec 128) :
    XBinOp.eval .pshufb a maskBA = ofDwords (dword a 0) (dword a 2) 0 0 := by
  rw [pshufb_BA_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega_using [hi], by omega_using [], by omega_using []⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega_using [],
    getLsbD_ofDwords_block _ _ _ _ (by omega_using [hk]) (by omega_using [hr])]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega_using [])
  all_goals
  simp (disch := omega_using [hr]) only [↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and] <;>
  simp

/-- `vpshufb` with `maskDC`: doublewords 0 and 2 into 2 and 3, zeros below. -/
theorem pshufb_DC (a : BitVec 128) :
    XBinOp.eval .pshufb a maskDC = ofDwords 0 0 (dword a 0) (dword a 2) := by
  rw [pshufb_DC_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega_using [hi], by omega_using [], by omega_using []⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega_using [],
    getLsbD_ofDwords_block _ _ _ _ (by omega_using [hk]) (by omega_using [hr])]
  match k, hk with
  | 0, _ => ?_
  | 1, _ => ?_
  | 2, _ => ?_
  | 3, _ => ?_
  | 4, _ => ?_
  | 5, _ => ?_
  | 6, _ => ?_
  | 7, _ => ?_
  | 8, _ => ?_
  | 9, _ => ?_
  | 10, _ => ?_
  | 11, _ => ?_
  | 12, _ => ?_
  | 13, _ => ?_
  | 14, _ => ?_
  | 15, _ => ?_
  | _ + 16, h => exact absurd h (by omega_using [])
  all_goals
  simp (disch := omega_using [hr]) only [↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and] <;>
  simp

theorem shufDwords_fa (a : BitVec 128) :
    shufDwords a 0xfa = ofDwords (dword a 2) (dword a 2) (dword a 3) (dword a 3) := rfl

theorem shufDwords_50 (a : BitVec 128) :
    shufDwords a 0x50 = ofDwords (dword a 0) (dword a 0) (dword a 1) (dword a 1) := rfl

theorem paddd_eq (a b : BitVec 128) :
    XBinOp.eval .paddd a b = ofDwords (dword a 0 + dword b 0) (dword a 1 + dword b 1)
      (dword a 2 + dword b 2) (dword a 3 + dword b 3) := rfl

theorem pxor_eq (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl

/-! ## One lane of `schedule` -/

/-- What `schedule` computes in one lane, from the lane's four message
registers `x₀ … x₃` (oldest first), as its instructions do. -/
def xupd (x₀ x₁ x₂ x₃ : BitVec 128) : BitVec 128 :=
  let t₀ := alignRight x₁ x₀ 4
  let t₃ := alignRight x₃ x₂ 4
  let t₂ := XShiftOp.eval .psrld t₀ 7
  let y := XBinOp.eval .paddd x₀ t₃
  let t₃ := XShiftOp.eval .psrld t₀ 3
  let t₁ := XShiftOp.eval .pslld t₀ 14
  let t₀ := XBinOp.eval .pxor t₃ t₂
  let t₃ := shufDwords x₃ 0xfa
  let t₂ := XShiftOp.eval .psrld t₂ 11
  let t₀ := XBinOp.eval .pxor t₀ t₁
  let t₁ := XShiftOp.eval .pslld t₁ 11
  let t₀ := XBinOp.eval .pxor t₀ t₂
  let t₂ := XShiftOp.eval .psrld t₃ 10
  let t₀ := XBinOp.eval .pxor t₀ t₁
  let t₃ := XShiftOp.eval .psrlq t₃ 17
  let y := XBinOp.eval .paddd y t₀
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₃ 2
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₂ := XBinOp.eval .pshufb t₂ maskBA
  let y := XBinOp.eval .paddd y t₂
  let t₃ := shufDwords y 0x50
  let t₂ := XShiftOp.eval .psrld t₃ 10
  let t₃ := XShiftOp.eval .psrlq t₃ 17
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₃ := XShiftOp.eval .psrlq t₃ 2
  let t₂ := XBinOp.eval .pxor t₂ t₃
  let t₂ := XBinOp.eval .pshufb t₂ maskDC
  XBinOp.eval .paddd y t₂

/-- `σ₀`, as `schedule` computes it: shifts by 3, 7, 14, 18 and 25. -/
theorem ssig0_shifts (x : Word) :
    (x >>> 3 ^^^ x >>> 7 ^^^ x <<< 14 ^^^ x >>> 7 >>> 11 ^^^ x <<< 14 <<< 11) = ssig0 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ssig0, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, decide_eq_true hi, Bool.true_and,
    show 7 + (11 + i) = 18 + i by omega_using []]
  by_cases h14 : i < 14
  · simp only [h14, show i < 25 by omega_using [h14], show i - 11 < 32 by omega_using [hi], show i - 11 < 14 by omega_using [h14],
      decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.xor_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h18 : x.getLsbD (18 + i) = false := BitVec.getLsbD_of_ge x _ (by omega_using [h14])
  by_cases h25 : i < 25
  · simp only [h14, h25, h18, show i - 11 < 32 by omega_using [hi], show i - 11 < 14 by omega_using [h25], decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_false,
      Bool.xor_false, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  · simp only [h14, h25, h18, BitVec.getLsbD_of_ge x (7 + i) (by omega_using [h25]),
      show ¬ i < 11 by omega_using [h14], show i - 11 < 32 by omega_using [hi], show ¬ i - 11 < 14 by omega_using [h25], decide_true,
      decide_false, Bool.not_false, Bool.true_and,
      Bool.xor_false, ite_false, Nat.sub_sub, Nat.reduceAdd]
    simp only [Bool.xor_comm, Bool.xor_assoc]


/-- `σ₁`, as `schedule` computes it: shifts of the word doubled into a quadword. -/
theorem ssig1_shifts (x : Word) :
    (x >>> 10 ^^^ (x >>> 17 ||| x <<< 15) ^^^ ((x >>> 17 ||| x <<< 15) >>> 2 ||| x >>> 17 <<< 30)) =
      ssig1 x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ssig1, BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_rotateRight, Nat.reduceMod, Nat.reduceSub, decide_eq_true hi, Bool.true_and,
    show 17 + (2 + i) = 19 + i by omega_using []]
  by_cases h13 : i < 13
  · simp only [h13, show i < 15 by omega_using [h13], show 2 + i < 15 by omega_using [h13], show i < 30 by omega_using [h13], decide_true,
      Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h19 : x.getLsbD (19 + i) = false := BitVec.getLsbD_of_ge x _ (by omega_using [h13])
  by_cases h15 : i < 15
  · simp only [h13, h15, h19, show ¬ 2 + i < 15 by omega_using [h13], show 2 + i < 32 by omega_using [h15],
      show i < 30 by omega_using [h15], show 2 + i - 15 = i - 13 by omega_using [], decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  have h17 : x.getLsbD (17 + i) = false := BitVec.getLsbD_of_ge x _ (by omega_using [h15])
  by_cases h30 : i < 30
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 15 by omega_using [h13], show 2 + i < 32 by omega_using [h30],
      show 2 + i - 15 = i - 13 by omega_using [], decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 32 by omega_using [h30], show 17 + (i - 30) = i - 13 by omega_using [h30],
      BitVec.getLsbD_of_ge x (10 + i) (by omega_using [h30]), decide_false,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.false_xor, Bool.xor_false, ite_false]

theorem word_add_zero (x : Word) : x + 0 = x := BitVec.add_zero x

/-- `schedule`, on one lane: from `W₄ᵢ₋₁₆ … W₄ᵢ₋₁` (`w₀ … w₁₅`), the next
four words. -/
theorem xupd_eq (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ w₁₄ w₁₅ : Word) :
    xupd (ofDwords w₀ w₁ w₂ w₃) (ofDwords w₄ w₅ w₆ w₇) (ofDwords w₈ w₉ w₁₀ w₁₁)
      (ofDwords w₁₂ w₁₃ w₁₄ w₁₅) =
      ofDwords (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄) (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)
        (w₂ + w₁₁ + ssig0 w₃ + ssig1 (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄))
        (w₃ + w₁₂ + ssig0 w₄ + ssig1 (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)) := by
  simp only [xupd, alignRight_4, psrld_eq _ _ (by decide : (7 : BitVec 8).toNat < 32),
    psrld_eq _ _ (by decide : (3 : BitVec 8).toNat < 32), psrld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    psrld_eq _ _ (by decide : (10 : BitVec 8).toNat < 32),
    pslld_eq _ _ (by decide : (14 : BitVec 8).toNat < 32), pslld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    pxor_eq, xor_ofDwords, paddd_eq, shufDwords_fa, shufDwords_50, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]
  simp only [psrlq_eq _ _ _ _ _ (by decide : (17 : BitVec 8).toNat < 32),
    psrlq_eq _ _ _ _ _ (by decide : (2 : BitVec 8).toNat < 32), pshufb_BA, pshufb_DC,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  simp only [BitVec.reduceToNat, Nat.reduceSub, ssig0_shifts, ssig1_shifts,
    word_add_zero]

/-- `schedule` computes the next four words of a block's schedule. -/
theorem xupd_quad (M : Block) (i : Nat) :
    xupd (quad M i) (quad M (i + 1)) (quad M (i + 2)) (quad M (i + 3)) = quad M (i + 4) := by
  simp only [quad]
  rw [xupd_eq]
  have w0 : W M (4 * (i + 4)) = ssig1 (W M (4 * (i + 3) + 2)) + W M (4 * (i + 2) + 1) +
      ssig0 (W M (4 * i + 1)) + W M (4 * i) := W_ge' M (4 * i)
  have w1 : W M (4 * (i + 4) + 1) = ssig1 (W M (4 * (i + 3) + 3)) + W M (4 * (i + 2) + 2) +
      ssig0 (W M (4 * i + 2)) + W M (4 * i + 1) := W_ge' M (4 * i + 1)
  have w2 : W M (4 * (i + 4) + 2) = ssig1 (W M (4 * (i + 4))) + W M (4 * (i + 2) + 3) +
      ssig0 (W M (4 * i + 3)) + W M (4 * i + 2) := W_ge' M (4 * i + 2)
  have w3 : W M (4 * (i + 4) + 3) = ssig1 (W M (4 * (i + 4) + 1)) + W M (4 * (i + 3)) +
      ssig0 (W M (4 * (i + 1))) + W M (4 * i + 3) := W_ge' M (4 * i + 3)
  rw [w2, w3, w0, w1]
  ac_rfl

end VG.Proof.Sha256.X86_64.Avx2

/-!
# SHA-256 with AVX2 on x86-64: running the message schedule

`schedule i` computes, in each lane of `msg i`, what `xupd` says, and stores
the register.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The vector registers of `schedule i` are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), t0, t1, t2, t3, mBA, mDC, mBswap, tmp].Nodup := by
  have key : ∀ c < 4,
      [msg c, msg (c + 1), msg (c + 2), msg (c + 3), t0, t1, t2, t3, mBA, mDC, mBswap, tmp].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega_using []]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The schedule of words `4i … 4i+3`, from lanes `a, b, c, d` (lane 0) and
`a', b', c', d'` (lane 1) of `msg i … msg (i+3)`. -/
theorem schedule_ok (i : Nat) (s : State) (a b c d a' b' c' d' : BitVec 128)
    (ha : s.xmm (msg i) = a) (hb : s.xmm (msg (i + 1)) = b) (hc : s.xmm (msg (i + 2)) = c)
    (hd : s.xmm (msg (i + 3)) = d) (ha' : s.ymmHi (msg i) = a') (hb' : s.ymmHi (msg (i + 1)) = b')
    (hc' : s.ymmHi (msg (i + 2)) = c') (hd' : s.ymmHi (msg (i + 3)) = d')
    (hBA : s.xmm mBA = maskBA) (hBA' : s.ymmHi mBA = maskBA)
    (hDC : s.xmm mDC = maskDC) (hDC' : s.ymmHi mDC = maskDC)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int)) 32) :
    WP isa (.block (schedule i)) s fun s' =>
      s'.xmm (msg i) = xupd a b c d ∧ s'.ymmHi (msg i) = xupd a' b' c' d' ∧
      (∀ r, r ≠ msg i → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int))
        (xupd a' b' c' d' ++ xupd a b c d) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup i
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [schedule, vb, vs]
  generalize msg i = x₀ at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 2) = x₂ at *
  generalize msg (i + 3) = x₃ at *
  simp only [t0, t1, t2, t3, mBA, mDC, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' hBA hBA' hDC hDC' ⊢
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, and_self, runBlock_cons, runStep_some, runBlock_nil, reduceExec, reduceVOpExec,
    isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, ea_at, hout, hn, hn',
    ha, hb, hc, hd, ha', hb', hc', hd', hBA, hBA', hDC, hDC', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

end VG.Proof.Sha256.X86_64.Avx2

end

end

/-!
# SHA-256 with AVX2 on x86-64: one round

`round j t` computes `roundKW`, with its additions reordered, `Σ₀` and `Σ₁` as
three `rorx`, `Ch` as a sum of two disjoint masks and `Maj` from the previous
round's `a ⊕ b`.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha256 (roundKW rounds_succ round_eq)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` is in `carry t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0].setWidth 64 ∧ s.gpr (var t 1) = v[1].setWidth 64 ∧
  s.gpr (var t 2) = v[2].setWidth 64 ∧ s.gpr (var t 3) = v[3].setWidth 64 ∧
  s.gpr (var t 4) = v[4].setWidth 64 ∧ s.gpr (var t 5) = v[5].setWidth 64 ∧
  s.gpr (var t 6) = v[6].setWidth 64 ∧ s.gpr (var t 7) = v[7].setWidth 64 ∧
  s.gpr (carry t) = (v[1] ^^^ v[2]).setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written
by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega_using []

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, carry t, carry (t + 1), T,
      .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  have e : carry (t + 1) = if t % 2 = 0 then .r14 else .r13 := by
    simp only [carry]; split <;> split <;> first | rfl | omega
  rw [e]
  simp only [var, carry]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega_using [])
  rw [show t % 2 = t % 8 % 2 by omega_using []]
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

theorem ch_add (e f g : Word) : ch e f g = (~~~e &&& g) + (e &&& f) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi
    simp only [ch, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_carry (a b c : Word) : maj a b c = (b ^^^ c) &&& (a ^^^ b) ^^^ b := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

/-- `T₁` in the order the round adds it. -/
theorem sum_T₁ (h k w c₁ c₂ s : Word) : h + k + w + c₁ + c₂ + s = h + s + (c₁ + c₂) + k + w := by
  ac_rfl

/-- `T₁ + T₂` in the order the round adds it. -/
theorem sum_T₁T₂ (h k w c₁ c₂ s s₀ m : Word) :
    h + k + w + c₁ + c₂ + s + s₀ + m = h + s + (c₁ + c₂) + k + w + (s₀ + m) := by
  ac_rfl

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the others). -/
theorem round_ok (j t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : Vars t s v) (hin : InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4)
    (hw : s.mem.readW (s.ea (wSlot j t)) 32 = w) :
    WP isa (.block (round j t)) s fun s' =>
      Vars (t + 1) s' (roundKW v (K t) w) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have hd := round_nodup t
  have hd' := VG.nodup_reverse hd
  simp only [Vars, var_succ_zero, var_succ t _ (show 0 < 7 by omega_using []),
    var_succ t _ (show 1 < 7 by omega_using []), var_succ t _ (show 2 < 7 by omega_using []),
    var_succ t _ (show 3 < 7 by omega_using []), var_succ t _ (show 4 < 7 by omega_using []),
    var_succ t _ (show 5 < 7 by omega_using []), var_succ t _ (show 6 < 7 by omega_using [])] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hc⟩ := hv
  have ea : s.ea (wSlot j t) = s.gpr .rcx + BitVec.ofInt 64 ((32 * (t / 4) + 16 * j + 4 * (t % 4) : Nat) : Int) :=
    rfl
  rw [ea] at hin hw
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86_64.Avx2.round, wSlot, at_]
  generalize var t 0 = a at *
  generalize var t 1 = b at *
  generalize var t 2 = c at *
  generalize var t 3 = d at *
  generalize var t 4 = e at *
  generalize var t 5 = f at *
  generalize var t 6 = g at *
  generalize var t 7 = h at *
  generalize carry t = x at *
  generalize carry (t + 1) = y at *
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' ⊢
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reducePow, runBlock_cons, runStep_some,
    runBlock_nil, reduceExec, execAlu32, execRorx32, execAndn32, readSrc32, State.ea,
    isa, State.load32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags,
    RegUpd.ymmHi_setFlags, 
    hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hc, hin, hw, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, and_self, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  rotate_left
  · simp only [pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hd']
  · simp only [roundKW, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ch_add, maj_carry, bsig0, bsig1,
      and_true, true_and]
    exact ⟨congrArg _ (sum_T₁T₂ ..), congrArg _ (congrArg _ (sum_T₁ ..))⟩

/-! ## Rounds of a block -/

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- Round `t` of block `j` can read `Wₜ` of `M`. -/
def WOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4 ∧ s.mem.readW (s.ea (wSlot j t)) 32 = W M t

theorem WOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : WOk j M s t) (hk : Keeps s s') :
    WOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hk.2.2.2.1 .rcx (by decide)]
  rw [WOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem round_step (j t : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : Vars t s (Spec.Sha256.rounds H M t)) (hw : WOk j M s t) :
    WP isa (.block (round j t)) s fun s' => Vars (t + 1) s' (Spec.Sha256.rounds H M (t + 1)) ∧ Keeps s s' := by
  rw [rounds_succ, round_eq]
  exact round_ok j t s _ _ hv hw.1 hw.2

theorem rounds4_ok (j n : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : Vars (4 * n) s (Spec.Sha256.rounds H M (4 * n))) (hw : ∀ q < 4, WOk j M s (4 * n + q)) :
    WP isa (.block (round j (4 * n) ++ round j (4 * n + 1) ++ round j (4 * n + 2) ++ round j (4 * n + 3))) s
      fun s' => Vars (4 * n + 4) s' (Spec.Sha256.rounds H M (4 * n + 4)) ∧ Keeps s s' := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (round_step j _ H M s hv (hw 0 (by omega_using []))) fun s₁ ⟨hv₁, hk₁⟩ => ?_
  refine WP.mono (round_step j _ H M s₁ hv₁ ((hw 1 (by omega_using [])).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ => ?_
  have hk₂' := hk₁.trans hk₂
  refine WP.mono (round_step j _ H M s₂ hv₂ ((hw 2 (by omega_using [])).keeps hk₂')) fun s₃ ⟨hv₃, hk₃⟩ => ?_
  have hk₃' := hk₂'.trans hk₃
  refine WP.mono (round_step j _ H M s₃ hv₃ ((hw 3 (by omega_using [])).keeps hk₃')) fun s₄ ⟨hv₄, hk₄⟩ => ?_
  exact ⟨hv₄, hk₃'.trans hk₄⟩

/-- The rounds of the second block. -/
theorem rounds2_ok (H : HashValue) (M : Block) (s : State) (hv : Vars 0 s H)
    (hw : ∀ t < 64, WOk 1 M s t) :
    ∀ n ≤ 64, WP isa (rounds2 n) s fun s' => Vars n s' (Spec.Sha256.rounds H M n) ∧ Keeps s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨hv, Keeps.refl s⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega_using [hn])) fun s₁ ⟨hv₁, hk₁⟩ => ?_)
    exact WP.mono (round_step 1 n H M s₁ hv₁ ((hw n (by omega_using [hn])).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ =>
      ⟨hv₂, hk₁.trans hk₂⟩

end VG.Proof.Sha256.X86_64.Avx2
