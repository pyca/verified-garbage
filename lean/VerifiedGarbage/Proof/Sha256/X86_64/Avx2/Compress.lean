import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Impl.Sha256.X86_64.Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Sha256.Spec
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lit`. -/
section

/-!
# SHA-256 with AVX2 on x86-64: the code as a literal

The compression function as a literal (`materialize_code`,
`Proof/Framework/Lit.lean`).
-/

namespace VG

materialize_code Impl.Sha256.X86_64.Avx2.compress

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Schedule`. -/
section

/-!
# SHA-256 with AVX2 on x86-64: the message schedule of one lane

Each 256-bit instruction of the schedule acts on the two 128-bit lanes alike,
so it is proved once, on one lane (`xupd`): the next four words of a block's
schedule from its previous sixteen.
-/

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
  apply ext_dword <;> simp only [VG.Proof.Sha256.X86_64.Avx2.dword_xor, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3]

theorem psrld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrld a n =
      ofDwords (dword a 0 >>> n.toNat) (dword a 1 >>> n.toNat) (dword a 2 >>> n.toNat)
        (dword a 3 >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]

theorem pslld_eq (a : BitVec 128) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .pslld a n =
      ofDwords (dword a 0 <<< n.toNat) (dword a 1 <<< n.toNat) (dword a 2 <<< n.toNat)
        (dword a 3 <<< n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 31 < n.toNat by omega, ite_false]

theorem qword_ofDwords_0 (a c b d : BitVec 32) : qword (ofDwords a c b d) 0 = c ++ a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero,
    Nat.zero_add, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 32
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 32 < 32 by omega, ite_true]

theorem qword_ofDwords_1 (a c b d : BitVec 32) : qword (ofDwords a c b d) 1 = d ++ b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, ofDwords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one,
    decide_eq_true hi, Bool.true_and, show ¬ 64 + i < 32 by omega, show ¬ 64 + i - 32 < 32 by omega,
    ite_false]
  by_cases h : i < 32
  · simp only [h, ite_true, show 64 + i - 32 - 32 = i by omega]
  · simp only [h, show ¬ 64 + i - 32 - 32 < 32 by omega, ite_false,
      show 64 + i - 32 - 32 - 32 = i - 32 by omega]

theorem shr_append (c a : BitVec 32) {m : Nat} (h : m < 32) :
    (c ++ a : BitVec 64) >>> m = (c >>> m) ++ (a >>> m ||| c <<< (32 - m)) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · by_cases h2 : m + i < 32
    · simp only [h1, h2, ite_true, decide_true, show i < 32 - m by omega, Bool.not_true, Bool.true_and,
        Bool.false_and, Bool.or_false]
    · simp only [h1, h2, ite_true, ite_false, decide_true, show ¬ i < 32 - m by omega, decide_false,
        Bool.not_false, Bool.true_and, BitVec.getLsbD_of_ge a (m + i) (by omega), Bool.false_or,
        show i - (32 - m) = m + i - 32 by omega]
  · simp only [h1, show ¬ m + i < 32 by omega, ite_false, show m + (i - 32) = m + i - 32 by omega]

theorem append_pairs (p q r s : BitVec 32) : (p ++ q) ++ (r ++ s) = ofDwords s r q p := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [ofDwords, BitVec.getLsbD_append]
  simp only [Nat.reduceAdd, Nat.sub_sub]
  by_cases h1 : i < 32
  · simp only [h1, show i < 64 by omega, ite_true]
  by_cases h2 : i < 64
  · simp only [h1, h2, show i - 32 < 32 by omega, ite_true, ite_false]
  by_cases h3 : i < 96
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega, show i - 64 < 32 by omega, ite_true, ite_false]
  · simp only [h1, h2, show ¬ i - 32 < 32 by omega, show ¬ i - 64 < 32 by omega, ite_false]

/-- A quadword shift right, on doublewords: the high doubleword of each
quadword shifts into the low one. -/
theorem psrlq_eq (a c b d : BitVec 32) (n : BitVec 8) (h : n.toNat < 32) :
    XShiftOp.eval .psrlq (ofDwords a c b d) n =
      ofDwords (a >>> n.toNat ||| c <<< (32 - n.toNat)) (c >>> n.toNat)
        (b >>> n.toNat ||| d <<< (32 - n.toNat)) (d >>> n.toNat) := by
  simp only [XShiftOp.eval, show ¬ 63 < n.toNat by omega, ite_false, VG.Proof.Sha256.X86_64.Avx2.qword_ofDwords_0,
    VG.Proof.Sha256.X86_64.Avx2.qword_ofDwords_1, VG.Proof.Sha256.X86_64.Avx2.shr_append _ _ h, VG.Proof.Sha256.X86_64.Avx2.append_pairs]

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
  rw [VG.Proof.Sha256.X86_64.Avx2.pshufb_BA_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
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
  | _ + 16, h => exact absurd h (by omega)
  all_goals
  simp (disch := omega) only [↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and] <;>
  simp

/-- `vpshufb` with `maskDC`: doublewords 0 and 2 into 2 and 3, zeros below. -/
theorem pshufb_DC (a : BitVec 128) :
    XBinOp.eval .pshufb a maskDC = ofDwords 0 0 (dword a 0) (dword a 2) := by
  rw [VG.Proof.Sha256.X86_64.Avx2.pshufb_DC_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
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
  | _ + 16, h => exact absurd h (by omega)
  all_goals
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
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
    show 7 + (11 + i) = 18 + i by omega]
  by_cases h14 : i < 14
  · simp only [h14, show i < 25 by omega, show i - 11 < 32 by omega, show i - 11 < 14 by omega,
      decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.xor_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h18 : x.getLsbD (18 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h25 : i < 25
  · simp only [h14, h25, h18, show i - 11 < 32 by omega, show i - 11 < 14 by omega, decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.and_false,
      Bool.xor_false, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  · simp only [h14, h25, h18, BitVec.getLsbD_of_ge x (7 + i) (by omega),
      show ¬ i < 11 by omega, show i - 11 < 32 by omega, show ¬ i - 11 < 14 by omega, decide_true,
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
    show 17 + (2 + i) = 19 + i by omega]
  by_cases h13 : i < 13
  · simp only [h13, show i < 15 by omega, show 2 + i < 15 by omega, show i < 30 by omega, decide_true,
      Bool.not_true, Bool.false_and, Bool.and_false, Bool.or_false, ite_true]
    simp only [Bool.xor_comm, Bool.xor_assoc]
  have h19 : x.getLsbD (19 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h15 : i < 15
  · simp only [h13, h15, h19, show ¬ 2 + i < 15 by omega, show 2 + i < 32 by omega,
      show i < 30 by omega, show 2 + i - 15 = i - 13 by omega, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_true, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  have h17 : x.getLsbD (17 + i) = false := BitVec.getLsbD_of_ge x _ (by omega)
  by_cases h30 : i < 30
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 15 by omega, show 2 + i < 32 by omega,
      show 2 + i - 15 = i - 13 by omega, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, ite_false]
    simp only [Bool.xor_comm, Bool.xor_left_comm]
  · simp only [h13, h15, h19, h17, h30, show ¬ 2 + i < 32 by omega, show 17 + (i - 30) = i - 13 by omega,
      BitVec.getLsbD_of_ge x (10 + i) (by omega), decide_false,
      Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false,
      Bool.false_or, Bool.false_xor, Bool.xor_false, ite_false]

theorem word_add_zero (x : Word) : x + 0 = x := BitVec.add_zero x

/-- `schedule`, on one lane: from `W₄ᵢ₋₁₆ … W₄ᵢ₋₁` (`w₀ … w₁₅`), the next
four words. -/
theorem xupd_eq (w₀ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈ w₉ w₁₀ w₁₁ w₁₂ w₁₃ w₁₄ w₁₅ : Word) :
    VG.Proof.Sha256.X86_64.Avx2.xupd (ofDwords w₀ w₁ w₂ w₃) (ofDwords w₄ w₅ w₆ w₇) (ofDwords w₈ w₉ w₁₀ w₁₁)
      (ofDwords w₁₂ w₁₃ w₁₄ w₁₅) =
      ofDwords (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄) (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)
        (w₂ + w₁₁ + ssig0 w₃ + ssig1 (w₀ + w₉ + ssig0 w₁ + ssig1 w₁₄))
        (w₃ + w₁₂ + ssig0 w₄ + ssig1 (w₁ + w₁₀ + ssig0 w₂ + ssig1 w₁₅)) := by
  simp only [VG.Proof.Sha256.X86_64.Avx2.xupd, alignRight_4, VG.Proof.Sha256.X86_64.Avx2.psrld_eq _ _ (by decide : (7 : BitVec 8).toNat < 32),
    VG.Proof.Sha256.X86_64.Avx2.psrld_eq _ _ (by decide : (3 : BitVec 8).toNat < 32), VG.Proof.Sha256.X86_64.Avx2.psrld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    VG.Proof.Sha256.X86_64.Avx2.psrld_eq _ _ (by decide : (10 : BitVec 8).toNat < 32),
    VG.Proof.Sha256.X86_64.Avx2.pslld_eq _ _ (by decide : (14 : BitVec 8).toNat < 32), VG.Proof.Sha256.X86_64.Avx2.pslld_eq _ _ (by decide : (11 : BitVec 8).toNat < 32),
    VG.Proof.Sha256.X86_64.Avx2.pxor_eq, VG.Proof.Sha256.X86_64.Avx2.xor_ofDwords, VG.Proof.Sha256.X86_64.Avx2.paddd_eq, VG.Proof.Sha256.X86_64.Avx2.shufDwords_fa, VG.Proof.Sha256.X86_64.Avx2.shufDwords_50, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]
  simp only [VG.Proof.Sha256.X86_64.Avx2.psrlq_eq _ _ _ _ _ (by decide : (17 : BitVec 8).toNat < 32),
    VG.Proof.Sha256.X86_64.Avx2.psrlq_eq _ _ _ _ _ (by decide : (2 : BitVec 8).toNat < 32), VG.Proof.Sha256.X86_64.Avx2.pshufb_BA, VG.Proof.Sha256.X86_64.Avx2.pshufb_DC,
    dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]
  simp only [BitVec.reduceToNat, Nat.reduceSub, VG.Proof.Sha256.X86_64.Avx2.ssig0_shifts, VG.Proof.Sha256.X86_64.Avx2.ssig1_shifts,
    VG.Proof.Sha256.X86_64.Avx2.word_add_zero]

/-- `schedule` computes the next four words of a block's schedule. -/
theorem xupd_quad (M : Block) (i : Nat) :
    VG.Proof.Sha256.X86_64.Avx2.xupd (quad M i) (quad M (i + 1)) (quad M (i + 2)) (quad M (i + 3)) = quad M (i + 4) := by
  simp only [quad]
  rw [VG.Proof.Sha256.X86_64.Avx2.xupd_eq]
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

theorem msg_add4 (n : Nat) : VG.Impl.Sha256.X86_64.Avx2.msg (n + 4) = VG.Impl.Sha256.X86_64.Avx2.msg n := by
  simp only [VG.Impl.Sha256.X86_64.Avx2.msg, Nat.add_mod_right]

/-- The vector registers of `schedule i` are all different. -/
theorem msg_nodup (n : Nat) :
    [VG.Impl.Sha256.X86_64.Avx2.msg n, VG.Impl.Sha256.X86_64.Avx2.msg (n + 1), VG.Impl.Sha256.X86_64.Avx2.msg (n + 2), VG.Impl.Sha256.X86_64.Avx2.msg (n + 3), t0, t1, t2, t3, mBA, mDC, mBswap, tmp].Nodup := by
  have key : ∀ c < 4,
      [VG.Impl.Sha256.X86_64.Avx2.msg c, VG.Impl.Sha256.X86_64.Avx2.msg (c + 1), VG.Impl.Sha256.X86_64.Avx2.msg (c + 2), VG.Impl.Sha256.X86_64.Avx2.msg (c + 3), t0, t1, t2, t3, mBA, mDC, mBswap, tmp].Nodup := by
    decide
  have e : ∀ k, VG.Impl.Sha256.X86_64.Avx2.msg (n + k) = VG.Impl.Sha256.X86_64.Avx2.msg (n % 4 + k) := fun k => by
    simp only [VG.Impl.Sha256.X86_64.Avx2.msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show VG.Impl.Sha256.X86_64.Avx2.msg n = VG.Impl.Sha256.X86_64.Avx2.msg (n % 4) by simp only [VG.Impl.Sha256.X86_64.Avx2.msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (VG.Impl.Sha256.X86_64.Avx2.at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The schedule of words `4i … 4i+3`, from lanes `a, b, c, d` (lane 0) and
`a', b', c', d'` (lane 1) of `msg i … msg (i+3)`. -/
theorem schedule_ok (i : Nat) (s : State) (a b c d a' b' c' d' : BitVec 128)
    (ha : s.xmm (VG.Impl.Sha256.X86_64.Avx2.msg i) = a) (hb : s.xmm (VG.Impl.Sha256.X86_64.Avx2.msg (i + 1)) = b) (hc : s.xmm (VG.Impl.Sha256.X86_64.Avx2.msg (i + 2)) = c)
    (hd : s.xmm (VG.Impl.Sha256.X86_64.Avx2.msg (i + 3)) = d) (ha' : s.ymmHi (VG.Impl.Sha256.X86_64.Avx2.msg i) = a') (hb' : s.ymmHi (VG.Impl.Sha256.X86_64.Avx2.msg (i + 1)) = b')
    (hc' : s.ymmHi (VG.Impl.Sha256.X86_64.Avx2.msg (i + 2)) = c') (hd' : s.ymmHi (VG.Impl.Sha256.X86_64.Avx2.msg (i + 3)) = d')
    (hBA : s.xmm mBA = maskBA) (hBA' : s.ymmHi mBA = maskBA)
    (hDC : s.xmm mDC = maskDC) (hDC' : s.ymmHi mDC = maskDC)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int)) 32) :
    WP isa (.block (VG.Impl.Sha256.X86_64.Avx2.schedule i)) s fun s' =>
      s'.xmm (VG.Impl.Sha256.X86_64.Avx2.msg i) = VG.Proof.Sha256.X86_64.Avx2.xupd a b c d ∧ s'.ymmHi (VG.Impl.Sha256.X86_64.Avx2.msg i) = VG.Proof.Sha256.X86_64.Avx2.xupd a' b' c' d' ∧
      (∀ r, r ≠ VG.Impl.Sha256.X86_64.Avx2.msg i → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int))
        (VG.Proof.Sha256.X86_64.Avx2.xupd a' b' c' d' ++ VG.Proof.Sha256.X86_64.Avx2.xupd a b c d) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := VG.Proof.Sha256.X86_64.Avx2.msg_nodup i
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [VG.Impl.Sha256.X86_64.Avx2.schedule, vb, vs]
  generalize VG.Impl.Sha256.X86_64.Avx2.msg i = x₀ at *
  generalize VG.Impl.Sha256.X86_64.Avx2.msg (i + 1) = x₁ at *
  generalize VG.Impl.Sha256.X86_64.Avx2.msg (i + 2) = x₂ at *
  generalize VG.Impl.Sha256.X86_64.Avx2.msg (i + 3) = x₃ at *
  simp only [t0, t1, t2, t3, mBA, mDC, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' hBA hBA' hDC hDC' ⊢
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceAdd, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.lane, State.ymm, State.store256, VG.Proof.Sha256.X86_64.Avx2.ea_at, hout, hn, hn',
    ha, hb, hc, hd, ha', hb', hc', hd', hBA, hBA', hDC, hDC', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

end VG.Proof.Sha256.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Rounds`. -/
section

/-!
# SHA-256 with AVX2 on x86-64: one round

`round j t` computes `roundKW`, with `Σ₀` and `Σ₁` as three `rorx`, `Ch` as a
sum of two disjoint masks and `Maj` from the previous round's `a ⊕ b`.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha256 (roundKW rounds_succ round_eq)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` is in `carry t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 0) = v[0].setWidth 64 ∧ s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 1) = v[1].setWidth 64 ∧
  s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 2) = v[2].setWidth 64 ∧ s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 3) = v[3].setWidth 64 ∧
  s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 4) = v[4].setWidth 64 ∧ s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 5) = v[5].setWidth 64 ∧
  s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 6) = v[6].setWidth 64 ∧ s.gpr (VG.Impl.Sha256.X86_64.Avx2.var t 7) = v[7].setWidth 64 ∧
  s.gpr (carry t) = (v[1] ^^^ v[2]).setWidth 64

/-- The registers that hold pointers and the count, and `rsp`: never written
by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 7) : VG.Impl.Sha256.X86_64.Avx2.var (t + 1) (k + 1) = VG.Impl.Sha256.X86_64.Avx2.var t k := by
  simp only [VG.Impl.Sha256.X86_64.Avx2.var]; congr 1; omega

theorem var_succ_zero (t : Nat) : VG.Impl.Sha256.X86_64.Avx2.var (t + 1) 0 = VG.Impl.Sha256.X86_64.Avx2.var t 7 := by
  simp only [VG.Impl.Sha256.X86_64.Avx2.var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [VG.Impl.Sha256.X86_64.Avx2.var t 0, VG.Impl.Sha256.X86_64.Avx2.var t 1, VG.Impl.Sha256.X86_64.Avx2.var t 2, VG.Impl.Sha256.X86_64.Avx2.var t 3, VG.Impl.Sha256.X86_64.Avx2.var t 4, VG.Impl.Sha256.X86_64.Avx2.var t 5, VG.Impl.Sha256.X86_64.Avx2.var t 6, VG.Impl.Sha256.X86_64.Avx2.var t 7, carry t, carry (t + 1), T,
      .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  have e : carry (t + 1) = if t % 2 = 0 then .r14 else .r13 := by
    simp only [carry]; split <;> split <;> first | rfl | omega
  rw [e]
  simp only [VG.Impl.Sha256.X86_64.Avx2.var, carry]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega)
  rw [show t % 2 = t % 8 % 2 by omega]
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

theorem ch_add (e f g : Word) : ch e f g = (e &&& f) + (~~~e &&& g) := by
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

/-- The round is symbolically executed once, for any registers `a … h`
(which `round_nodup` says are different from each other and the others). -/
theorem round_ok (j t : Nat) (s : State) (v : HashValue) (w : Word)
    (hv : VG.Proof.Sha256.X86_64.Avx2.Vars t s v) (hin : InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4)
    (hw : s.mem.readW (s.ea (wSlot j t)) 32 = w) :
    WP isa (.block (VG.Impl.Sha256.X86_64.Avx2.round j t)) s fun s' =>
      VG.Proof.Sha256.X86_64.Avx2.Vars (t + 1) s' (roundKW v (K t) w) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s'.gpr r = s.gpr r) ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have hd := VG.Proof.Sha256.X86_64.Avx2.round_nodup t
  have hd' := VG.nodup_reverse hd
  simp only [VG.Proof.Sha256.X86_64.Avx2.Vars, VG.Proof.Sha256.X86_64.Avx2.var_succ_zero, VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 0 < 7 by omega),
    VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 1 < 7 by omega), VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 2 < 7 by omega),
    VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 3 < 7 by omega), VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 4 < 7 by omega),
    VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 5 < 7 by omega), VG.Proof.Sha256.X86_64.Avx2.var_succ t _ (show 6 < 7 by omega)] at hv ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, hc⟩ := hv
  have ea : s.ea (wSlot j t) = s.gpr .rcx + BitVec.ofInt 64 ((32 * (t / 4) + 16 * j + 4 * (t % 4) : Nat) : Int) :=
    rfl
  rw [ea] at hin hw
  apply WP.of_runBlock
  simp only [Impl.Sha256.X86_64.Avx2.round, wSlot, VG.Impl.Sha256.X86_64.Avx2.at_]
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 0 = a at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 1 = b at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 2 = c at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 3 = d at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 4 = e at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 5 = f at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 6 = g at *
  generalize VG.Impl.Sha256.X86_64.Avx2.var t 7 = h at *
  generalize carry t = x at *
  generalize carry (t + 1) = y at *
  simp only [T, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, or_false, not_or,
    List.nodup_nil, and_true] at hd hd' ⊢
  simp only [↓reduceIte, Nat.reduceLeDiff, Nat.reducePow, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, execRorx32, execAndn32, readSrc32, State.ea,
    isa, State.load32, State.setReg32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags,
    RegUpd.ymmHi_setFlags,
    hd, hd', h0, h1, h2, h3, h4, h5, h6, h7, hc, hin, hw, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, and_self, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  rotate_left
  · simp only [VG.Proof.Sha256.X86_64.Avx2.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [hd']
  · simp only [roundKW, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, VG.Proof.Sha256.X86_64.Avx2.ch_add, VG.Proof.Sha256.X86_64.Avx2.maj_carry, bsig0, bsig1, BitVec.add_assoc,
      and_self]

/-! ## Rounds of a block -/

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : VG.Proof.Sha256.X86_64.Avx2.Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Sha256.X86_64.Avx2.Keeps s₁ s₂) (h₂ : VG.Proof.Sha256.X86_64.Avx2.Keeps s₂ s₃) : VG.Proof.Sha256.X86_64.Avx2.Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- Round `t` of block `j` can read `Wₜ` of `M`. -/
def WOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4 ∧ s.mem.readW (s.ea (wSlot j t)) 32 = W M t

theorem WOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : VG.Proof.Sha256.X86_64.Avx2.WOk j M s t) (hk : VG.Proof.Sha256.X86_64.Avx2.Keeps s s') :
    VG.Proof.Sha256.X86_64.Avx2.WOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, VG.Impl.Sha256.X86_64.Avx2.at_, hk.2.2.2.1 .rcx (by decide)]
  rw [VG.Proof.Sha256.X86_64.Avx2.WOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

theorem round_step (j t : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : VG.Proof.Sha256.X86_64.Avx2.Vars t s (Spec.Sha256.rounds H M t)) (hw : VG.Proof.Sha256.X86_64.Avx2.WOk j M s t) :
    WP isa (.block (VG.Impl.Sha256.X86_64.Avx2.round j t)) s fun s' => VG.Proof.Sha256.X86_64.Avx2.Vars (t + 1) s' (Spec.Sha256.rounds H M (t + 1)) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  rw [rounds_succ, round_eq]
  exact VG.Proof.Sha256.X86_64.Avx2.round_ok j t s _ _ hv hw.1 hw.2

theorem rounds4_ok (j n : Nat) (H : HashValue) (M : Block) (s : State)
    (hv : VG.Proof.Sha256.X86_64.Avx2.Vars (4 * n) s (Spec.Sha256.rounds H M (4 * n))) (hw : ∀ q < 4, VG.Proof.Sha256.X86_64.Avx2.WOk j M s (4 * n + q)) :
    WP isa (.block (VG.Impl.Sha256.X86_64.Avx2.round j (4 * n) ++ VG.Impl.Sha256.X86_64.Avx2.round j (4 * n + 1) ++ VG.Impl.Sha256.X86_64.Avx2.round j (4 * n + 2) ++ VG.Impl.Sha256.X86_64.Avx2.round j (4 * n + 3))) s
      fun s' => VG.Proof.Sha256.X86_64.Avx2.Vars (4 * n + 4) s' (Spec.Sha256.rounds H M (4 * n + 4)) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.round_step j _ H M s hv (hw 0 (by omega))) fun s₁ ⟨hv₁, hk₁⟩ => ?_
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.round_step j _ H M s₁ hv₁ ((hw 1 (by omega)).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ => ?_
  have hk₂' := hk₁.trans hk₂
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.round_step j _ H M s₂ hv₂ ((hw 2 (by omega)).keeps hk₂')) fun s₃ ⟨hv₃, hk₃⟩ => ?_
  have hk₃' := hk₂'.trans hk₃
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.round_step j _ H M s₃ hv₃ ((hw 3 (by omega)).keeps hk₃')) fun s₄ ⟨hv₄, hk₄⟩ => ?_
  exact ⟨hv₄, hk₃'.trans hk₄⟩

/-- The rounds of the second block. -/
theorem rounds2_ok (H : HashValue) (M : Block) (s : State) (hv : VG.Proof.Sha256.X86_64.Avx2.Vars 0 s H)
    (hw : ∀ t < 64, VG.Proof.Sha256.X86_64.Avx2.WOk 1 M s t) :
    ∀ n ≤ 64, WP isa (rounds2 n) s fun s' => VG.Proof.Sha256.X86_64.Avx2.Vars n s' (Spec.Sha256.rounds H M n) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨hv, Keeps.refl s⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s₁ ⟨hv₁, hk₁⟩ => ?_)
    exact WP.mono (VG.Proof.Sha256.X86_64.Avx2.round_step 1 n H M s₁ hv₁ ((hw n (by omega)).keeps hk₁)) fun s₂ ⟨hv₂, hk₂⟩ =>
      ⟨hv₂, hk₁.trans hk₂⟩

end VG.Proof.Sha256.X86_64.Avx2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress`. -/
section

/-!
# SHA-256 with AVX2 on x86-64: the rounds of the first block

Group `n` computes the message words `4n+16 … 4n+19` of both blocks, stores
them, and runs rounds `4n … 4n+3` of the first block, which read their words
from the scratch space. The words of both blocks are then all stored, for the
rounds of the second one.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W)
open VG.Proof.Sha256.X86_64.ShaNi (quad)
open VG.Proof.Sha256.X86_64 (ofInt_natCast contains_offset')

/-- Where `schedule` and `load` store the words `4k … 4k+3` of both blocks. -/
abbrev wAddr (scr : Addr) (k : Nat) : Addr := scr + BitVec.ofInt 64 ((32 * k : Nat) : Int)

/-- The words `4k … 4k+3` of `M₀` and `M₁` are stored, in lanes 0 and 1. -/
def WMem (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) : Prop :=
  m.readW (VG.Proof.Sha256.X86_64.Avx2.wAddr scr k) 256 = quad M₁ k ++ quad M₀ k

/-- The part of the scratch space holding the words. -/
abbrev wRegion (scr : Addr) : Region := ⟨scr, 512⟩

/-- The masks that `schedule` and `load` use. -/
def Masks (s : State) : Prop :=
  s.xmm mBA = maskBA ∧ s.ymmHi mBA = maskBA ∧ s.xmm mDC = maskDC ∧ s.ymmHi mDC = maskDC ∧
    s.xmm mBswap = bswapMask ∧ s.ymmHi mBswap = bswapMask

theorem extract_lane0 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 4) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 0 + 4 * q)) (8 * 4) = dword x₀ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, show 8 * (16 * 0 + 4 * q) + i < 128 by omega,
    ite_true]
  exact congrArg _ (by omega)

theorem extract_lane1 (x₁ x₀ : BitVec 128) {q : Nat} (hq : q < 4) :
    (x₁ ++ x₀).extractLsb' (8 * (16 * 1 + 4 * q)) (8 * 4) = dword x₁ q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, decide_eq_true hi, Bool.true_and, show ¬ 8 * (16 * 1 + 4 * q) + i < 128 by omega,
    ite_false]
  exact congrArg _ (by omega)

theorem dword_quad (M : Block) (k : Nat) {q : Nat} (hq : q < 4) : dword (quad M k) q = W M (4 * k + q) := by
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp [quad, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

theorem wSlot_ea (s : State) (j t : Nat) :
    s.ea (wSlot j t) = VG.Proof.Sha256.X86_64.Avx2.wAddr (s.gpr .rcx) (t / 4) + BitVec.ofNat 64 (16 * j + 4 * (t % 4)) := by
  simp only [State.ea, wSlot, at_, VG.Proof.Sha256.X86_64.Avx2.wAddr, ofInt_natCast]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]

theorem in_scr {s : State} {scr : Addr} (hR : (⟨scr, 560⟩ : Region) ∈ s.wr) {d n : Nat} (hd : d + n ≤ 560) :
    InRegions s.wr (scr + BitVec.ofInt 64 (d : Int)) n :=
  ⟨_, hR, contains_offset' hd (by omega)⟩

/-- Rounds read the words `WMem` says are stored. -/
theorem wok_of_wmem {s : State} {scr : Addr} {M₀ M₁ : Block} {t : Nat} (ht : t < 64)
    (hrcx : s.gpr .rcx = scr) (hR : (⟨scr, 560⟩ : Region) ∈ s.wr) (h : VG.Proof.Sha256.X86_64.Avx2.WMem s.mem scr M₀ M₁ (t / 4)) :
    VG.Proof.Sha256.X86_64.Avx2.WOk 0 M₀ s t ∧ VG.Proof.Sha256.X86_64.Avx2.WOk 1 M₁ s t := by
  have hin : ∀ j < 2, InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 4 := by
    intro j hj
    have e : s.ea (wSlot j t) = scr + BitVec.ofInt 64 ((32 * (t / 4) + 16 * j + 4 * (t % 4) : Nat) : Int) := by
      simp only [State.ea, wSlot, at_, hrcx]
    rw [e]
    obtain ⟨r, hr, hc⟩ := VG.Proof.Sha256.X86_64.Avx2.in_scr hR (d := 32 * (t / 4) + 16 * j + 4 * (t % 4)) (n := 4) (by omega)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have rd : ∀ j < 2, s.mem.readW (s.ea (wSlot j t)) 32 =
      (quad M₁ (t / 4) ++ quad M₀ (t / 4)).extractLsb' (8 * (16 * j + 4 * (t % 4))) (8 * 4) := by
    intro j hj
    rw [VG.Proof.Sha256.X86_64.Avx2.wSlot_ea, hrcx, ← h, readW_extract _ _ (by omega)]
  have et : 4 * (t / 4) + t % 4 = t := by omega
  refine ⟨⟨hin 0 (by omega), ?_⟩, ⟨hin 1 (by omega), ?_⟩⟩
  · rw [rd 0 (by omega), VG.Proof.Sha256.X86_64.Avx2.extract_lane0 _ _ (Nat.mod_lt _ (by omega)), VG.Proof.Sha256.X86_64.Avx2.dword_quad _ _ (Nat.mod_lt _ (by omega)),
      et]
  · rw [rd 1 (by omega), VG.Proof.Sha256.X86_64.Avx2.extract_lane1 _ _ (Nat.mod_lt _ (by omega)), VG.Proof.Sha256.X86_64.Avx2.dword_quad _ _ (Nat.mod_lt _ (by omega)),
      et]

theorem wmem_write {m : Mem} {scr : Addr} {M₀ M₁ : Block} {k k' : Nat} (hk : k < 16) (hk' : k' < 16)
    (hne : k ≠ k') (v : BitVec 256) (h : VG.Proof.Sha256.X86_64.Avx2.WMem m scr M₀ M₁ k) :
    VG.Proof.Sha256.X86_64.Avx2.WMem (m.writeW (VG.Proof.Sha256.X86_64.Avx2.wAddr scr k') v) scr M₀ M₁ k := by
  simp only [VG.Proof.Sha256.X86_64.Avx2.WMem, VG.Proof.Sha256.X86_64.Avx2.wAddr, ofInt_natCast] at h ⊢
  exact (readW_writeW_off m scr v (d := 32 * k) (e := 32 * k') (n := 32) (by omega) (by omega)
    (by omega)).trans h

theorem wmem_self (m : Mem) (scr : Addr) (M₀ M₁ : Block) (k : Nat) :
    VG.Proof.Sha256.X86_64.Avx2.WMem (m.writeW (VG.Proof.Sha256.X86_64.Avx2.wAddr scr k) (quad M₁ k ++ quad M₀ k)) scr M₀ M₁ k :=
  Mem.readW_writeW_self m _ 32 _ (by omega)

theorem wAddr_contains (scr : Addr) {k : Nat} (hk : k < 16) : (VG.Proof.Sha256.X86_64.Avx2.wRegion scr).Contains (VG.Proof.Sha256.X86_64.Avx2.wAddr scr k) (256 / 8) :=
  contains_offset' (by omega) (by omega)

/-! ## The groups -/

/-- What holds of the schedule after `n` groups, relative to the state `sB`
at their start. -/
structure Sched (M₀ M₁ : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop where
  pub : ∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  masks : VG.Proof.Sha256.X86_64.Avx2.Masks s
  frame : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion scr] sB.mem s.mem
  wmem : ∀ k < 16, k < n + 4 → VG.Proof.Sha256.X86_64.Avx2.WMem s.mem scr M₀ M₁ k
  msgs : ∀ k, n ≤ k → k < n + 4 → k < 16 → s.xmm (msg k) = quad M₀ k ∧ s.ymmHi (msg k) = quad M₁ k

theorem Sched.keeps {M₀ M₁ : Block} {scr : Addr} {sB : State} {n : Nat} {s s' : State}
    (h : VG.Proof.Sha256.X86_64.Avx2.Sched M₀ M₁ scr sB n s) (hk : VG.Proof.Sha256.X86_64.Avx2.Keeps s s') : VG.Proof.Sha256.X86_64.Avx2.Sched M₀ M₁ scr sB n s' := by
  obtain ⟨hm, hrd, hwr, hpub, hx, hy⟩ := hk
  refine ⟨fun r hr => (hpub r hr).trans (h.pub r hr), hrd.trans h.rd, hwr.trans h.wr, ?_, hm ▸ h.frame,
    fun k hk hk' => hm ▸ h.wmem k hk hk', fun k h₁ h₂ h₃ => hx ▸ hy ▸ h.msgs k h₁ h₂ h₃⟩
  rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx, hy]; exact h.masks

/-- The registers `schedule` writes. -/
theorem sched_other (n : Nat) (r : XReg) (h : r = mBA ∨ r = mDC ∨ r = mBswap ∨ r = tmp) :
    r ≠ msg n ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 := by
  have key : ∀ c < 4, ∀ r ∈ [mBA, mDC, mBswap, tmp],
      r ≠ msg c ∧ r ≠ t0 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ t3 := by decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

theorem msg_ne (n k : Nat) (h₁ : n < k) (h₂ : k ≤ n + 3) : msg k ≠ msg n ∧ msg k ≠ t0 ∧ msg k ≠ t1 ∧
    msg k ≠ t2 ∧ msg k ≠ t3 := by
  have key : ∀ c < 4, ∀ d < 4, 0 < d →
      msg (c + d) ≠ msg c ∧ msg (c + d) ≠ t0 ∧ msg (c + d) ≠ t1 ∧ msg (c + d) ≠ t2 ∧ msg (c + d) ≠ t3 := by
    decide
  rw [show msg k = msg (n % 4 + (k - n)) by simp only [msg]; rw [show (n % 4 + (k - n)) % 4 = k % 4 by omega],
    show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) _ (by omega) (by omega)

theorem sched_step {M₀ M₁ : Block} {scr : Addr} {sB : State} (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sB.wr) {n : Nat} (hn : n < 16) {s : State} (h : VG.Proof.Sha256.X86_64.Avx2.Sched M₀ M₁ scr sB n s) :
    WP isa (.block (if n < 12 then schedule (n + 4) else [])) s fun s' =>
      VG.Proof.Sha256.X86_64.Avx2.Sched M₀ M₁ scr sB (n + 1) s' ∧ s'.gpr = s.gpr := by
  by_cases h12 : n < 12
  · simp only [h12, ↓reduceIte]
    have hrcx' : s.gpr .rcx = scr := (h.pub .rcx (by decide)).trans hrcx
    have m : ∀ q < 4, s.xmm (msg (n + 4 + q)) = quad M₀ (n + q) ∧ s.ymmHi (msg (n + 4 + q)) = quad M₁ (n + q) :=
      fun q hq => by
        rw [show n + 4 + q = n + q + 4 by omega, VG.Proof.Sha256.X86_64.Avx2.msg_add4]
        exact h.msgs (n + q) (by omega) (by omega) (by omega)
    obtain ⟨ma, ma'⟩ := m 0 (by omega)
    obtain ⟨mb, mb'⟩ := m 1 (by omega)
    obtain ⟨mc, mc'⟩ := m 2 (by omega)
    obtain ⟨md, md'⟩ := m 3 (by omega)
    obtain ⟨k1, k2, k3, k4, _, _⟩ := h.masks
    simp only [Nat.add_zero] at ma ma'
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.schedule_ok (n + 4) s _ _ _ _ _ _ _ _ ma mb mc md ma' mb' mc' md' k1 k2 k3 k4
      (by rw [hrcx', h.wr]; exact VG.Proof.Sha256.X86_64.Avx2.in_scr hR (by omega)))
      fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hg⟩
    rw [VG.Proof.Sha256.X86_64.Avx2.xupd_quad] at ex ey
    rw [VG.Proof.Sha256.X86_64.Avx2.xupd_quad, VG.Proof.Sha256.X86_64.Avx2.xupd_quad, hrcx'] at hm
    refine ⟨fun r hr => by rw [hg]; exact h.pub r hr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
    · have o := fun r hr => hx r (VG.Proof.Sha256.X86_64.Avx2.sched_other (n + 4) r hr).1 (VG.Proof.Sha256.X86_64.Avx2.sched_other (n + 4) r hr).2.1
        (VG.Proof.Sha256.X86_64.Avx2.sched_other (n + 4) r hr).2.2.1 (VG.Proof.Sha256.X86_64.Avx2.sched_other (n + 4) r hr).2.2.2.1 (VG.Proof.Sha256.X86_64.Avx2.sched_other (n + 4) r hr).2.2.2.2
      have masks := h.masks
      rw [VG.Proof.Sha256.X86_64.Avx2.Masks, (o mBA (by simp)).1, (o mBA (by simp)).2, (o mDC (by simp)).1, (o mDC (by simp)).2,
        (o mBswap (by simp)).1, (o mBswap (by simp)).2]
      exact masks
    · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86_64.Avx2.wAddr_contains scr (by omega))
    · intro k hk hk'
      rw [hm]
      by_cases hkn : k = n + 4
      · subst hkn; exact VG.Proof.Sha256.X86_64.Avx2.wmem_self _ _ _ _ _
      · exact VG.Proof.Sha256.X86_64.Avx2.wmem_write hk (by omega) hkn _ (h.wmem k hk (by omega))
    · intro k h₁ h₂ h₃
      by_cases hkn : k = n + 4
      · subst hkn; exact ⟨ex, ey⟩
      · have o := VG.Proof.Sha256.X86_64.Avx2.msg_ne (n + 4) (k + 4) (by omega) (by omega)
        rw [VG.Proof.Sha256.X86_64.Avx2.msg_add4] at o
        rw [(hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).1, (hx _ o.1 o.2.1 o.2.2.1 o.2.2.2.1 o.2.2.2.2).2]
        exact h.msgs k (by omega) (by omega) h₃
  · simp only [h12, ↓reduceIte]
    exact WP.block_nil ⟨⟨h.pub, h.rd, h.wr, h.masks, h.frame, fun k hk _ => h.wmem k hk (by omega),
      fun k h₁ _ h₃ => h.msgs k (by omega) (by omega) h₃⟩, rfl⟩

/-- After `n` groups. -/
def GInv (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (n : Nat) (s : State) : Prop :=
  VG.Proof.Sha256.X86_64.Avx2.Vars (4 * n) s (Spec.Sha256.rounds H M₀ (4 * n)) ∧ VG.Proof.Sha256.X86_64.Avx2.Sched M₀ M₁ scr sB n s

theorem groups_ok (H : HashValue) (M₀ M₁ : Block) (scr : Addr) (sB : State) (hrcx : sB.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sB.wr) (h₀ : VG.Proof.Sha256.X86_64.Avx2.GInv H M₀ M₁ scr sB 0 sB) :
    ∀ n ≤ 16, WP isa (groups n) sB (VG.Proof.Sha256.X86_64.Avx2.GInv H M₀ M₁ scr sB n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h₀
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s ⟨hv, hs⟩ => ?_)
    have e : group n = (if n < 12 then schedule (n + 4) else []) ++
        (round 0 (4 * n) ++ round 0 (4 * n + 1) ++ round 0 (4 * n + 2) ++ round 0 (4 * n + 3)) := by
      simp only [group, List.append_assoc]
    rw [e, WP.block_append_iff]
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.sched_step hrcx hR (by omega) hs) fun s₁ ⟨hs₁, hg₁⟩ => ?_
    have hv₁ : VG.Proof.Sha256.X86_64.Avx2.Vars (4 * n) s₁ (Spec.Sha256.rounds H M₀ (4 * n)) := by simp only [VG.Proof.Sha256.X86_64.Avx2.Vars, hg₁]; exact hv
    have hrcx₁ : s₁.gpr .rcx = scr := (hs₁.pub .rcx (by decide)).trans hrcx
    have hR₁ : (⟨scr, 560⟩ : Region) ∈ s₁.wr := hs₁.wr ▸ hR
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.rounds4_ok 0 n H M₀ s₁ hv₁ fun q hq => (VG.Proof.Sha256.X86_64.Avx2.wok_of_wmem (by omega) hrcx₁ hR₁
      (hs₁.wmem _ (by omega) (by omega))).1) fun s₂ ⟨hv₂, hk₂⟩ => ?_
    rw [show 4 * n + 4 = 4 * (n + 1) by omega] at hv₂
    exact ⟨hv₂, hs₁.keeps hk₂⟩

end VG.Proof.Sha256.X86_64.Avx2

/-!
# SHA-256 compression function on x86-64 with AVX2 and BMI

`compress_verified` proves `Impl.Sha256.X86_64.Avx2.compress` against the same
contract as the scalar `vg_sha256_compress`, reusing its precondition (`Pre`)
and block lemmas.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha256.X86_64.ShaNi (quad load_quad)
open VG.Proof.Sha256.X86_64 (Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' sub_offset toNat_ofNat_lt ofInt_natCast stateAt_get stateAt_eq
  readW_writeW_word writeState stateAt_writeState frame_writeState)

/-! ## The prologue -/

/-- The callee-saved registers are saved in the scratch space. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (scr s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 8 ≤ 560 := by decide

/-- The memory after the prologue. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (scr s₀) s₀.gpr saved

set_option simprocs false in
theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ const mBswap bswapMask ++ const mBA maskBA ++ const mDC maskDC ++
      ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s₁ =>
      (∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Sha256.X86_64.Avx2.saveMem s₀ ∧
      s₁.zf = some (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) ∧ VG.Proof.Sha256.X86_64.Avx2.Masks s₁ := by
  simp only [List.append_assoc]
  refine Spill.save_then .rcx saved (fun p hp' => ?_) ?_
  · have := VG.Proof.Sha256.X86_64.Avx2.saved_bound p hp'
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.of_runBlock
  simp only [const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, VOp.exec, State.setV, State.lane,
    State.setReg, arithFlags, State.setFlags, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr], trivial, trivial, trivial, trivial, ?_⟩
  simp (config := {decide := true}) only [VG.Proof.Sha256.X86_64.Avx2.Masks, mBA, mDC, mBswap, ite_true, ite_false, VBinOp.sse,
    movq_const, and_self]

/-! ## Loading the blocks -/

theorem load_ok {i : Nat} (hi : i < 4) (s : State) {p₀ p₁ scr : Addr} {M₀ M₁ : Block}
    (hrsi : s.gpr .rsi = p₀) (hr15 : s.gpr .r15 = p₁) (hrcx : s.gpr .rcx = scr)
    (hin₀ : InRegions (s.rd ++ s.wr) (p₀ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hin₁ : InRegions (s.rd ++ s.wr) (p₁ + BitVec.ofInt 64 ((16 * i : Nat) : Int)) 16)
    (hout : InRegions s.wr (VG.Proof.Sha256.X86_64.Avx2.wAddr scr i) 32)
    (hm : s.xmm mBswap = bswapMask) (hm' : s.ymmHi mBswap = bswapMask)
    (hb₀ : ∀ t : Nat, t < 16 → bswap32 (s.mem.readW (p₀ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₀ t)
    (hb₁ : ∀ t : Nat, t < 16 → bswap32 (s.mem.readW (p₁ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₁ t) :
    WP isa (.block (load i)) s fun s' =>
      s'.xmm (msg i) = quad M₀ i ∧ s'.ymmHi (msg i) = quad M₁ i ∧
      (∀ r, r ≠ msg i → r ≠ tmp → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem.writeW (VG.Proof.Sha256.X86_64.Avx2.wAddr scr i) (quad M₁ i ++ quad M₀ i) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := VG.Proof.Sha256.X86_64.Avx2.msg_nodup i
  have hd' := VG.nodup_reverse hd
  have q₀ := load_quad M₀ s.mem p₀ hi hb₀
  have q₁ := load_quad M₁ s.mem p₁ hi hb₁
  have e : bswapMask = Impl.Sha256.X86_64.ShaNi.bswapMask := rfl
  rw [← e] at q₀ q₁
  apply WP.of_runBlock
  simp only [load, vb]
  generalize msg i = x at *
  simp only [T, t0, t1, t2, t3, mBA, mDC, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd' hm hm' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.lane, State.ymm, State.store256, State.load128, VG.Proof.Sha256.X86_64.Avx2.ea_at, hrsi, hr15, hrcx, hin₀,
    hin₁, hout, ite_true, ite_false, hd, hd', hm, hm', VBinOp.sse, q₀, q₁, Option.map_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## The hash value -/

/-- The working variables `v` are in the registers of round 0. -/
def Vars8 (s : State) (v : HashValue) : Prop :=
  s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
  s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
  s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
  s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64

theorem Vars.vars8 {s : State} {v : HashValue} (h : VG.Proof.Sha256.X86_64.Avx2.Vars 64 s v) : VG.Proof.Sha256.X86_64.Avx2.Vars8 s v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem loadState_eq : loadState = [
    .mov32 .rax (.mem (at_ .rdi (4 * 0))), .mov32 .rbx (.mem (at_ .rdi (4 * 1))),
    .mov32 .rbp (.mem (at_ .rdi (4 * 2))), .mov32 .r8 (.mem (at_ .rdi (4 * 3))),
    .mov32 .r9 (.mem (at_ .rdi (4 * 4))), .mov32 .r10 (.mem (at_ .rdi (4 * 5))),
    .mov32 .r11 (.mem (at_ .rdi (4 * 6))), .mov32 .r12 (.mem (at_ .rdi (4 * 7)))] := by
  decide

theorem addState_eq : addState = [
    .alu32 .add .rax (.mem (at_ .rdi (4 * 0))), .alu32 .add .rbx (.mem (at_ .rdi (4 * 1))),
    .alu32 .add .rbp (.mem (at_ .rdi (4 * 2))), .alu32 .add .r8 (.mem (at_ .rdi (4 * 3))),
    .alu32 .add .r9 (.mem (at_ .rdi (4 * 4))), .alu32 .add .r10 (.mem (at_ .rdi (4 * 5))),
    .alu32 .add .r11 (.mem (at_ .rdi (4 * 6))), .alu32 .add .r12 (.mem (at_ .rdi (4 * 7))),
    .store32 (at_ .rdi (4 * 0)) .rax, .store32 (at_ .rdi (4 * 1)) .rbx,
    .store32 (at_ .rdi (4 * 2)) .rbp, .store32 (at_ .rdi (4 * 3)) .r8,
    .store32 (at_ .rdi (4 * 4)) .r9, .store32 (at_ .rdi (4 * 5)) .r10,
    .store32 (at_ .rdi (4 * 6)) .r11, .store32 (at_ .rdi (4 * 7)) .r12] := by
  decide

theorem initCarry_eq : initCarry = [.mov32 .r13 (.reg .rbx), .alu32 .xor .r13 (.reg .rbp)] := rfl

set_option simprocs false in
theorem loadState_ok {s₀ : State} (hp : Pre s₀) {s : State} (hrdi : s.gpr .rdi = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block loadState) s fun s₁ => VG.Proof.Sha256.X86_64.Avx2.Vars8 s₁ (stateAt s.mem (st s₀)) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s₁ := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  apply WP.of_runBlock
  rw [VG.Proof.Sha256.X86_64.Avx2.loadState_eq]
  have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
  have h3 := hin 3 (by decide); have h4 := hin 4 (by decide); have h5 := hin 5 (by decide)
  have h6 := hin 6 (by decide); have h7 := hin 7 (by decide)
  simp (config := {decide := true}) only [VG.Proof.Sha256.X86_64.Avx2.Vars8, VG.Proof.Sha256.X86_64.Avx2.Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, VG.Proof.Sha256.X86_64.Avx2.ea_at,
    State.load32, State.setReg32, State.setReg, hrdi, h0, h1, h2, h3, h4, h5, h6, h7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [stateAt_get _ _ (show 0 < 8 by decide), stateAt_get _ _ (show 1 < 8 by decide),
    stateAt_get _ _ (show 2 < 8 by decide), stateAt_get _ _ (show 3 < 8 by decide),
    stateAt_get _ _ (show 4 < 8 by decide), stateAt_get _ _ (show 5 < 8 by decide),
    stateAt_get _ _ (show 6 < 8 by decide), stateAt_get _ _ (show 7 < 8 by decide)]
  simp (config := {decide := true}) [VG.Proof.Sha256.X86_64.Avx2.pubRegs]

theorem vars0 (s : State) (v : HashValue) : VG.Proof.Sha256.X86_64.Avx2.Vars 0 s v ↔
    s.gpr .rax = v[0].setWidth 64 ∧ s.gpr .rbx = v[1].setWidth 64 ∧
    s.gpr .rbp = v[2].setWidth 64 ∧ s.gpr .r8 = v[3].setWidth 64 ∧
    s.gpr .r9 = v[4].setWidth 64 ∧ s.gpr .r10 = v[5].setWidth 64 ∧
    s.gpr .r11 = v[6].setWidth 64 ∧ s.gpr .r12 = v[7].setWidth 64 ∧
    s.gpr .r13 = (v[1] ^^^ v[2]).setWidth 64 := Iff.rfl

theorem initCarry_ok {s : State} {v : HashValue} (hv : VG.Proof.Sha256.X86_64.Avx2.Vars8 s v) :
    WP isa (.block initCarry) s fun s₁ => VG.Proof.Sha256.X86_64.Avx2.Vars 0 s₁ v ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s₁ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  apply WP.of_runBlock
  rw [VG.Proof.Sha256.X86_64.Avx2.initCarry_eq]
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, VG.Proof.Sha256.X86_64.Avx2.vars0, VG.Proof.Sha256.X86_64.Avx2.Keeps, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32, isa, State.setReg32, State.setReg, arithFlags, State.setFlags,
    h0, h1, h2, h3, h4, h5, h6, h7, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, fun r hr => by
    simp only [VG.Proof.Sha256.X86_64.Avx2.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl, trivial⟩

set_option simprocs false in
theorem addState_ok {s₀ : State} (hp : Pre s₀) {s : State} (V H : HashValue) (hv : VG.Proof.Sha256.X86_64.Avx2.Vars8 s V)
    (hrdi : s.gpr .rdi = st s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hH : ∀ k : Nat, (hk : k < 8) →
      s.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = H[k]) :
    WP isa (.block addState) s fun s' =>
      s'.mem = writeState s.mem (st s₀) (Vector.zipWith (· + ·) V H) ∧
      VG.Proof.Sha256.X86_64.Avx2.Vars8 s' (Vector.zipWith (· + ·) V H) ∧
      (∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hin : ∀ k : Nat, k < 8 →
      InRegions (s.rd ++ s.wr) (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hrd, hwr]; exact fun k hk => hp.in_state hk
  have hout : ∀ k : Nat, k < 8 →
      InRegions s.wr (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 := by
    rw [hwr]; exact fun k hk => hp.out_state hk
  have i0 := hin 0 (by decide); have i1 := hin 1 (by decide); have i2 := hin 2 (by decide)
  have i3 := hin 3 (by decide); have i4 := hin 4 (by decide); have i5 := hin 5 (by decide)
  have i6 := hin 6 (by decide); have i7 := hin 7 (by decide)
  have o0 := hout 0 (by decide); have o1 := hout 1 (by decide); have o2 := hout 2 (by decide)
  have o3 := hout 3 (by decide); have o4 := hout 4 (by decide); have o5 := hout 5 (by decide)
  have o6 := hout 6 (by decide); have o7 := hout 7 (by decide)
  have m0 := hH 0 (by decide); have m1 := hH 1 (by decide); have m2 := hH 2 (by decide)
  have m3 := hH 3 (by decide); have m4 := hH 4 (by decide); have m5 := hH 5 (by decide)
  have m6 := hH 6 (by decide); have m7 := hH 7 (by decide)
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := hv
  apply WP.of_runBlock
  rw [VG.Proof.Sha256.X86_64.Avx2.addState_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu32, readSrc32,
    isa, VG.Proof.Sha256.X86_64.Avx2.ea_at, State.load32, State.store32, State.setReg32, State.setReg, arithFlags,
    State.setFlags, hrdi, i0, i1, i2, i3, i4, i5, i6, i7, o0, o1, o2, o3, o4, o5, o6, o7,
    m0, m1, m2, m3, m4, m5, m6, m7, v0, v1, v2, v3, v4, v5, v6, v7, ite_true, ite_false,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, trivial⟩
  · simp only [writeState, Vector.getElem_zipWith]
  · simp (config := {decide := true}) only [VG.Proof.Sha256.X86_64.Avx2.Vars8, Vector.getElem_zipWith, ite_true, ite_false, and_self]
  · simp only [VG.Proof.Sha256.X86_64.Avx2.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After loading words `0 … 4n-1` of both blocks, from the state `sL`. -/
structure LdInv (M₀ M₁ : Block) (scr : Addr) (sL : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = sL.gpr
  rd : s.rd = sL.rd
  wr : s.wr = sL.wr
  masks : VG.Proof.Sha256.X86_64.Avx2.Masks s
  frame : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion scr] sL.mem s.mem
  wmem : ∀ k < n, VG.Proof.Sha256.X86_64.Avx2.WMem s.mem scr M₀ M₁ k
  msgs : ∀ k < n, s.xmm (msg k) = quad M₀ k ∧ s.ymmHi (msg k) = quad M₁ k

theorem load_step {M₀ M₁ : Block} {p₀ p₁ scr : Addr} {sL : State}
    (hrsi : sL.gpr .rsi = p₀) (hr15 : sL.gpr .r15 = p₁) (hrcx : sL.gpr .rcx = scr)
    (hR : (⟨scr, 560⟩ : Region) ∈ sL.wr)
    (hin : ∀ n : Nat, n < 4 → InRegions (sL.rd ++ sL.wr) (p₀ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (sL.rd ++ sL.wr) (p₁ + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ m, Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion scr] sL.mem m →
      (∀ t : Nat, t < 16 → bswap32 (m.readW (p₀ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₀ t) ∧
      (∀ t : Nat, t < 16 → bswap32 (m.readW (p₁ + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M₁ t))
    {n : Nat} (hn : n < 4) {s : State} (h : VG.Proof.Sha256.X86_64.Avx2.LdInv M₀ M₁ scr sL n s) :
    WP isa (.block (load n)) s (VG.Proof.Sha256.X86_64.Avx2.LdInv M₀ M₁ scr sL (n + 1)) := by
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h.masks
  have hb := hblk _ h.frame
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.load_ok (p₀ := p₀) (p₁ := p₁) (scr := scr) (M₀ := M₀) (M₁ := M₁) hn s (by rw [h.gpr]; exact hrsi) (by rw [h.gpr]; exact hr15)
    (by rw [h.gpr]; exact hrcx) (by rw [h.rd, h.wr]; exact (hin n hn).1) (by rw [h.rd, h.wr]; exact (hin n hn).2)
    (by rw [h.wr]; exact VG.Proof.Sha256.X86_64.Avx2.in_scr hR (by omega)) k5 k6 hb.1 hb.2)
    fun s' ⟨ex, ey, hx, hg, hm, hrd, hwr⟩ => ⟨hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr, ?_, ?_, ?_, ?_⟩
  · have o := fun r (hr : r = mBA ∨ r = mDC ∨ r = mBswap) =>
      hx r (VG.Proof.Sha256.X86_64.Avx2.sched_other n r (by rcases hr with h | h | h <;> simp [h])).1 (by rcases hr with rfl | rfl | rfl <;> decide)
    rw [VG.Proof.Sha256.X86_64.Avx2.Masks, (o mBA (by simp)).1, (o mBA (by simp)).2, (o mDC (by simp)).1, (o mDC (by simp)).2,
      (o mBswap (by simp)).1, (o mBswap (by simp)).2]
    exact ⟨k1, k2, k3, k4, k5, k6⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.Sha256.X86_64.Avx2.wAddr_contains scr (by omega))
  · intro k hk
    rw [hm]
    by_cases hkn : k = n
    · subst hkn; exact VG.Proof.Sha256.X86_64.Avx2.wmem_self _ _ _ _ _
    · exact VG.Proof.Sha256.X86_64.Avx2.wmem_write (by omega) (by omega) hkn _ (h.wmem k (by omega))
  · intro k hk
    by_cases hkn : k = n
    · subst hkn; exact ⟨ex, ey⟩
    · have o₁ := (VG.Proof.Sha256.X86_64.Avx2.msg_ne k n (by omega) (by omega)).1
      have o₂ := (VG.Proof.Sha256.X86_64.Avx2.sched_other k tmp (by simp)).1
      rw [(hx _ (Ne.symm o₁) (Ne.symm o₂)).1, (hx _ (Ne.symm o₁) (Ne.symm o₂)).2]
      exact h.msgs k (by omega)

/-! ## Counting the blocks -/

theorem e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
theorem e2 : BitVec.signExtend 64 (2 : BitVec 32) = 2 := by decide
theorem e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
theorem e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide

theorem pub_ne15 {r : Reg} (hr : r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs) : r ≠ .r15 := by
  simp only [VG.Proof.Sha256.X86_64.Avx2.pubRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem setup_ok (s : State) :
    WP isa (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr .r15 = s.gpr .rsi ∧
      (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [T, VG.Proof.Sha256.X86_64.Avx2.Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, VG.Proof.Sha256.X86_64.Avx2.e1, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, fun r hr => by simp [hr], trivial, trivial, trivial,
    fun r hr => by simp [VG.Proof.Sha256.X86_64.Avx2.pub_ne15 hr], trivial⟩

theorem next_ok (s : State) :
    WP isa (.block [.alu .add T (.imm 64)]) s fun s' =>
      s'.gpr .r15 = s.gpr .r15 + 64 ∧ (∀ r, r ≠ .r15 → s'.gpr r = s.gpr r) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reducePow, and_self, T, VG.Proof.Sha256.X86_64.Avx2.Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, VG.Proof.Sha256.X86_64.Avx2.e64, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, fun r hr => by simp [VG.Proof.Sha256.X86_64.Avx2.pub_ne15 hr], trivial⟩

theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      eval .e s' = some (s.gpr .rdx - 1 == 0) ∧ s'.gpr = s.gpr ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s' := by
  apply WP.of_runBlock
  simp only [and_self, implies_true, VG.Proof.Sha256.X86_64.Avx2.Keeps, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, arithFlags, State.setFlags, VG.Proof.Sha256.X86_64.Avx2.e1, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial⟩

theorem adv_ok (s : State) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, and_self, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, isa, State.setReg, arithFlags, State.setFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨by simp [eval], trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩

/-! ## Regions -/

theorem wsub (p : Addr) : Region.Sub (VG.Proof.Sha256.X86_64.Avx2.wRegion p) ⟨p, 560⟩ := Region.sub_prefix (by omega)

theorem slot_sub (p : Addr) {d n : Nat} (hd : d + n ≤ 560) :
    Region.Sub ⟨p + BitVec.ofInt 64 (d : Int), n⟩ ⟨p, 560⟩ := by
  rw [ofInt_natCast]; exact sub_offset (by omega) (by omega)

theorem saved_frame {s₀ : State} (hp : Pre s₀) {m m' : Mem} (h : VG.Proof.Sha256.X86_64.Avx2.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion (scr s₀)] m m' ∨ Frame [stR s₀] m m') : VG.Proof.Sha256.X86_64.Avx2.Saved s₀ m' := by
  rcases hf with hf | hf <;> refine Spill.Saved.frame h hf fun p hp' r hr => ?_ <;>
    rw [List.mem_singleton.mp hr] <;> have := VG.Proof.Sha256.X86_64.Avx2.saved_bound p hp'
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Region.Disjoint.sub_left hp.st_scr.symm (Offset.sub_base _ (by omega))

theorem wmem_frame_st {s₀ : State} (hp : Pre s₀) {m m' : Mem} {M₀ M₁ : Block} {k : Nat} (hk : k < 16)
    (h : VG.Proof.Sha256.X86_64.Avx2.WMem m (scr s₀) M₀ M₁ k) (hf : Frame [stR s₀] m m') : VG.Proof.Sha256.X86_64.Avx2.WMem m' (scr s₀) M₀ M₁ k := by
  simp only [VG.Proof.Sha256.X86_64.Avx2.WMem] at h ⊢
  rw [← h]
  have hd := Region.Disjoint.sub_left hp.st_scr.symm (VG.Proof.Sha256.X86_64.Avx2.slot_sub (scr s₀) (d := 32 * k) (n := 32) (by omega))
  exact hf.readW (Region.contains_self _ _) (by simp only [List.mem_singleton, forall_eq]; exact hd)
    (by decide)

theorem state_frame_w {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion (scr s₀)] m m') :
    stateAt m' (st s₀) = stateAt m (st s₀) := by
  apply stateAt_eq
  intro k hk
  rw [hf.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
    (by simpa using Region.Disjoint.sub_right hp.st_scr (VG.Proof.Sha256.X86_64.Avx2.wsub _)) (by decide), ← stateAt_get _ _ hk]

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = st s₀
  rcx : s.gpr .rcx = scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt s.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i
  saved : VG.Proof.Sha256.X86_64.Avx2.Saved s₀ s.mem
  masks : VG.Proof.Sha256.X86_64.Avx2.Masks s

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86_64.Avx2.Common s₀ i s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

/-- The block in lane 1: the next one if there is one, else block `i` again. -/
abbrev nxt (s₀ : State) (i : Nat) : Nat := if nb s₀ - i = 1 then i else i + 1

/-- After the first block of an iteration. -/
structure Mid (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86_64.Avx2.Common s₀ (i + 1) s where
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)
  vars : VG.Proof.Sha256.X86_64.Avx2.Vars8 s (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))
  wmem : ∀ k < 16, VG.Proof.Sha256.X86_64.Avx2.WMem s.mem (scr s₀) (blk s₀ i) (blk s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i)) k
  e : eval .e s = some (nb s₀ - i == 1)

theorem sub_one_eq {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (BitVec.ofNat 64 (nb s₀ - i) - 1 == 0) = (nb s₀ - i == 1) := by
  have := hp.nb_lt
  have hn : nb s₀ - i < 2 ^ 64 := by omega
  have h1 : 1 ≤ nb s₀ - i := by omega
  generalize nb s₀ - i = n at *
  by_cases h : n = 1
  · subst h; decide
  · have h' : BitVec.ofNat 64 n - 1 ≠ 0 := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat h1]
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact h (by have h2 : n - 1 = 0 := this; omega)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

theorem blk_read {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {m m' : Mem}
    (hf : Frame [stR s₀, scrR s₀] s₀.mem m) (hf' : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion (scr s₀)] m m') :
    ∀ t : Nat, t < 16 → bswap32 (m'.readW (blkAddr s₀ i + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) =
      W (blk s₀ i) t := by
  intro t ht
  rw [hf'.readW (hp.blk_contains hi ht) (by simpa using Region.Disjoint.sub_right hp.blk_scr (VG.Proof.Sha256.X86_64.Avx2.wsub _)) (by decide),
    hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
  exact blk_word i t ht

/-- The first block of an iteration, up to the choice of whether there is a second. -/
theorem first_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : VG.Proof.Sha256.X86_64.Avx2.LInv s₀ i s)
    {G : Prog isa} {Q : State → Prop} (hG : ∀ s', VG.Proof.Sha256.X86_64.Avx2.Mid s₀ i s' → WP isa G s' Q) :
    WP isa (.seq (.block [.mov T (.reg .rsi), .alu .cmp .rdx (.imm 1)])
      (.seq (.ite .e (.block []) (.block [.alu .add T (.imm 64)]))
      (.seq (.block (load 0 ++ load 1 ++ load 2 ++ load 3 ++ loadState ++ initCarry))
      (.seq (groups 16)
      (.seq (.block addState)
      (.seq (.block [.alu .cmp .rdx (.imm 1)]) G)))))) s Q := by
  have := hp.nb_lt
  have hscr : (⟨scr s₀, 560⟩ : Region) ∈ s₀.wr := by simp [hp.wr]
  have hj : VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i < nb s₀ := by simp only [VG.Proof.Sha256.X86_64.Avx2.nxt]; split <;> omega
  have hb : (s.gpr .rdx - 1 == 0) = (nb s₀ - i == 1) := by rw [hL.rdx]; exact VG.Proof.Sha256.X86_64.Avx2.sub_one_eq hp hi
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.setup_ok s) fun s₁ ⟨he₁, h15₁, hg₁, hk₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r15 = blkAddr s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i) ∧
    (∀ r, r ≠ .r15 → s₂.gpr r = s.gpr r) ∧ VG.Proof.Sha256.X86_64.Avx2.Keeps s s₂) ?_ fun s₂ ⟨h15₂, hg₂, hk₂⟩ => ?_)
  · refine WP.ite _ he₁ (fun h => ?_) (fun h => ?_)
    · rw [hb, beq_iff_eq] at h
      refine WP.block_nil ⟨?_, hg₁, hk₁⟩
      simp only [VG.Proof.Sha256.X86_64.Avx2.nxt, h, ↓reduceIte, h15₁, hL.rsi]
    · refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.next_ok s₁) fun s₂ ⟨e15, eg, ek⟩ =>
        ⟨?_, fun r hr => (eg r hr).trans (hg₁ r hr), hk₁.trans ek⟩
      rw [hb, beq_eq_false_iff_ne] at h
      rw [e15, h15₁, hL.rsi]
      simp only [VG.Proof.Sha256.X86_64.Avx2.nxt, h, ↓reduceIte, blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 1) = 64 * i + 64 by omega]
  obtain ⟨hm₂, hrd₂, hwr₂, -, hx₂, hy₂⟩ := hk₂
  have pub₂ : ∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s₂.gpr r = s.gpr r := fun r hr => hg₂ r (VG.Proof.Sha256.X86_64.Avx2.pub_ne15 hr)
  have hrsi₂ : s₂.gpr .rsi = blkAddr s₀ i := (pub₂ .rsi (by decide)).trans hL.rsi
  have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hL.rcx
  have hrdi₂ : s₂.gpr .rdi = st s₀ := (pub₂ .rdi (by decide)).trans hL.rdi
  have hR₂ : (⟨scr s₀, 560⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hL.wr]; exact hscr
  have hf₂ : Frame [stR s₀, scrR s₀] s₀.mem s₂.mem := hm₂ ▸ hL.frame
  have hin : ∀ n : Nat, n < 4 →
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 ∧
      InRegions (s₂.rd ++ s₂.wr) (blkAddr s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i) + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 :=
    fun n hn => by rw [hrd₂, hwr₂, hL.rd, hL.wr]; exact ⟨ShaNi.Pre.in_blk16 hp hi hn, ShaNi.Pre.in_blk16 hp hj hn⟩
  have hblk := fun m (hm : Frame [VG.Proof.Sha256.X86_64.Avx2.wRegion (scr s₀)] s₂.mem m) =>
    And.intro (VG.Proof.Sha256.X86_64.Avx2.blk_read hp hi hf₂ hm) (VG.Proof.Sha256.X86_64.Avx2.blk_read hp hj hf₂ hm)
  have step := fun {n : Nat} (hn : n < 4) {x : State} (h : VG.Proof.Sha256.X86_64.Avx2.LdInv (blk s₀ i) (blk s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i)) (scr s₀) s₂ n x) =>
    VG.Proof.Sha256.X86_64.Avx2.load_step hrsi₂ h15₂ hrcx₂ hR₂ hin hblk hn h
  have h₀ : VG.Proof.Sha256.X86_64.Avx2.LdInv (blk s₀ i) (blk s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i)) (scr s₀) s₂ 0 s₂ :=
    ⟨rfl, rfl, rfl, by rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx₂, hy₂]; exact hL.masks, Frame.refl _ _, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (step (by omega) h₀) fun x₁ h₁ => ?_
  refine WP.mono (step (by omega) h₁) fun x₂ h₂ => ?_
  refine WP.mono (step (by omega) h₂) fun x₃ h₃ => ?_
  refine WP.mono (step (by omega) h₃) fun s₃ ld => ?_
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.loadState_ok hp (by rw [ld.gpr]; exact hrdi₂) (by rw [ld.rd, hrd₂, hL.rd])
    (by rw [ld.wr, hwr₂, hL.wr])) fun s₄ ⟨hv₄, hk₄⟩ => ?_
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.initCarry_ok hv₄) fun s₅ ⟨hv₅, hk₅⟩ => ?_
  have hk₃₅ := hk₄.trans hk₅
  obtain ⟨hm₅, hrd₅, hwr₅, pub₅, hx₅, hy₅⟩ := hk₃₅
  have hrcx₅ : s₅.gpr .rcx = scr s₀ := by rw [pub₅ .rcx (by decide), ld.gpr]; exact hrcx₂
  have hR₅ : (⟨scr s₀, 560⟩ : Region) ∈ s₅.wr := by rw [hwr₅, ld.wr]; exact hR₂
  have hS : VG.Proof.Sha256.X86_64.Avx2.Sched (blk s₀ i) (blk s₀ (VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i)) (scr s₀) s₅ 0 s₅ :=
    ⟨fun _ _ => rfl, rfl, rfl, by rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx₅, hy₅]; exact ld.masks, Frame.refl _ _,
      fun k _ hk => by rw [hm₅]; exact ld.wmem k (by omega),
      fun k _ hk _ => by rw [hx₅, hy₅]; exact ld.msgs k (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.groups_ok _ _ _ _ s₅ hrcx₅ hR₅ ⟨hv₅, hS⟩ 16 (Nat.le_refl _)) fun s₆ ⟨hv₆, hS₆⟩ => ?_)
  have hHi : stateAt s₃.mem (st s₀) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) i := by
    rw [VG.Proof.Sha256.X86_64.Avx2.state_frame_w hp ld.frame, hm₂]; exact hL.state
  have pub₆ : ∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s₆.gpr r = s.gpr r := fun r hr => by
    rw [hS₆.pub r hr, pub₅ r hr, ld.gpr, pub₂ r hr]
  have hrd₆ : s₆.rd = s₀.rd := by rw [hS₆.rd, hrd₅, ld.rd, hrd₂, hL.rd]
  have hwr₆ : s₆.wr = s₀.wr := by rw [hS₆.wr, hwr₅, ld.wr, hwr₂, hL.wr]
  have hH₆ : ∀ k : Nat, (hk : k < 8) →
      s₆.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 = (stateAt s₃.mem (st s₀))[k] :=
    fun k hk => by rw [← stateAt_get _ _ hk, VG.Proof.Sha256.X86_64.Avx2.state_frame_w hp hS₆.frame, hm₅]
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.addState_ok hp _ _ (Vars.vars8 hv₆) ((pub₆ .rdi (by decide)).trans hL.rdi) hrd₆ hwr₆
    hH₆) fun s₇ ⟨hm₇, hv₇, pub₇, hrd₇, hwr₇, hx₇, hy₇⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.cmp_ok s₇) fun s₈ ⟨he₈, hg₈, hk₈⟩ => hG s₈ ?_)
  obtain ⟨hm₈, hrd₈, hwr₈, -, hx₈, hy₈⟩ := hk₈
  have pub₈ : ∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s₈.gpr r = s.gpr r := fun r hr => by rw [hg₈, pub₇ r hr, pub₆ r hr]
  have hc : Vector.zipWith (· + ·) (Spec.Sha256.rounds (stateAt s₃.mem (st s₀)) (blk s₀ i) (4 * 16))
      (stateAt s₃.mem (st s₀)) = compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1) := by
    rw [compressBlocks_succ, ← hHi]; rfl
  have hfw : Frame [stR s₀] s₆.mem s₇.mem := by
    rw [hm₇]; exact frame_writeState (Frame.refl _ _) _
  have hsub : ∀ r ∈ [VG.Proof.Sha256.X86_64.Avx2.wRegion (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact VG.Proof.Sha256.X86_64.Avx2.wsub _⟩
  have hsub' : ∀ r ∈ [stR s₀], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pub₈ .rdi (by decide)]; exact hL.rdi
  · rw [pub₈ .rcx (by decide)]; exact hL.rcx
  · rw [pub₈ .rsp (by decide)]; exact hL.rsp
  · rw [hrd₈, hrd₇]; exact hrd₆
  · rw [hwr₈, hwr₇]; exact hwr₆
  · rw [hm₈]
    refine hf₂.trans ((ld.frame.sub hsub).trans ?_)
    rw [← hm₅]
    exact (hS₆.frame.sub hsub).trans (hfw.sub hsub')
  · rw [hm₈, hm₇, stateAt_writeState]; exact hc
  · rw [hm₈]
    refine VG.Proof.Sha256.X86_64.Avx2.saved_frame hp ?_ (.inr hfw)
    refine VG.Proof.Sha256.X86_64.Avx2.saved_frame hp ?_ (.inl hS₆.frame)
    rw [hm₅]
    refine VG.Proof.Sha256.X86_64.Avx2.saved_frame hp ?_ (.inl ld.frame)
    rw [hm₂]; exact hL.saved
  · rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx₈, hy₈, hx₇, hy₇]; exact hS₆.masks
  · rw [pub₈ .rsi (by decide)]; exact hL.rsi
  · rw [pub₈ .rdx (by decide)]; exact hL.rdx
  · simp only [VG.Proof.Sha256.X86_64.Avx2.Vars8, hg₈]; rw [← hc]; exact hv₇
  · intro k hk
    rw [hm₈]
    exact VG.Proof.Sha256.X86_64.Avx2.wmem_frame_st hp hk (hS₆.wmem k hk (by omega)) hfw
  · rw [he₈, pub₇ .rdx (by decide), pub₆ .rdx (by decide), hb]

/-! ## The end of an iteration -/

theorem adv_common {s₀ : State} {k : Nat} {s : State} (hc : VG.Proof.Sha256.X86_64.Avx2.Common s₀ k s) (a b : BitVec 32) :
    WP isa (.block [.alu .add .rsi (.imm a), .alu .sub .rdx (.imm b)]) s fun s' =>
      VG.Proof.Sha256.X86_64.Avx2.Common s₀ k s' ∧ eval .ne s' = some (!(s.gpr .rdx - b.signExtend 64 == 0)) ∧
      s'.gpr .rsi = s.gpr .rsi + a.signExtend 64 ∧ s'.gpr .rdx = s.gpr .rdx - b.signExtend 64 := by
  refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.adv_ok s a b) fun s' ⟨he, hrsi, hrdx, hg, hm, hrd, hwr, hx, hy⟩ => ⟨?_, he, hrsi, hrdx⟩
  refine ⟨by rw [hg _ (by decide) (by decide)]; exact hc.rdi, by rw [hg _ (by decide) (by decide)]; exact hc.rcx,
    by rw [hg _ (by decide) (by decide)]; exact hc.rsp, hrd.trans hc.rd, hwr.trans hc.wr, hm ▸ hc.frame,
    hm ▸ hc.state, hm ▸ hc.saved, ?_⟩
  rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx, hy]; exact hc.masks

/-- The loop exits after the last block, or goes on with block `k`. -/
theorem exit_or_next {s₀ : State} (hp : Pre s₀) {i k : Nat} (hk : i < k) (hk' : k ≤ nb s₀) {s : State}
    (hc : VG.Proof.Sha256.X86_64.Avx2.Common s₀ k s) (hrsi : s.gpr .rsi = blkAddr s₀ k) (hrdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - k))
    (he : eval .ne s = some (!(BitVec.ofNat 64 (nb s₀ - k) == 0))) :
    (eval .ne s = some false ∧ VG.Proof.Sha256.X86_64.Avx2.Common s₀ (nb s₀) s) ∨
      (eval .ne s = some true ∧ ∃ i', i < i' ∧ i' < nb s₀ ∧ VG.Proof.Sha256.X86_64.Avx2.LInv s₀ i' s) := by
  by_cases hlast : k = nb s₀
  · left
    subst hlast
    refine ⟨by rw [he]; simp, hc⟩
  · right
    have := hp.nb_lt
    have h0 : BitVec.ofNat 64 (nb s₀ - k) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      simp at h'
      omega
    refine ⟨by rw [he]; simpa using h0, k, hk, by omega, { hc with rsi := hrsi, rdx := hrdx }⟩

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : VG.Proof.Sha256.X86_64.Avx2.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha256.X86_64.Avx2.Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ i', i < i' ∧ i' < nb s₀ ∧ VG.Proof.Sha256.X86_64.Avx2.LInv s₀ i' s') := by
  have := hp.nb_lt
  have hn := (s₀.gpr .rdx).isLt
  refine VG.Proof.Sha256.X86_64.Avx2.first_ok hp hi hL fun s₁ hM => WP.ite _ hM.e (fun h => ?_) (fun h => ?_)
  · rw [beq_iff_eq] at h
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.adv_common hM.toCommon 64 1) fun s₂ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₁.gpr .rdx - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
      rw [hM.rdx, VG.Proof.Sha256.X86_64.Avx2.e1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    refine VG.Proof.Sha256.X86_64.Avx2.exit_or_next hp (by omega) (by omega) hc ?_ hrdx he
    rw [hrsi, hM.rsi, VG.Proof.Sha256.X86_64.Avx2.e64]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 1) = 64 * i + 64 by omega]
  · rw [beq_eq_false_iff_ne] at h
    have hnx : VG.Proof.Sha256.X86_64.Avx2.nxt s₀ i = i + 1 := by simp only [VG.Proof.Sha256.X86_64.Avx2.nxt, h, ↓reduceIte]
    have hw := hM.wmem
    rw [hnx] at hw
    refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.initCarry_ok hM.vars) fun s₂ ⟨hv₂, hk₂⟩ => ?_)
    obtain ⟨hm₂, hrd₂, hwr₂, pub₂, hx₂, hy₂⟩ := hk₂
    have hR₂ : (⟨scr s₀, 560⟩ : Region) ∈ s₂.wr := by rw [hwr₂, hM.wr, hp.wr]; simp
    have hrcx₂ : s₂.gpr .rcx = scr s₀ := (pub₂ .rcx (by decide)).trans hM.rcx
    refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.rounds2_ok _ (blk s₀ (i + 1)) s₂ hv₂ (fun t ht =>
      (VG.Proof.Sha256.X86_64.Avx2.wok_of_wmem ht hrcx₂ hR₂ (by rw [hm₂]; exact hw (t / 4) (by omega))).2) 64 (Nat.le_refl _))
      fun s₃ ⟨hv₃, hk₃⟩ => ?_)
    obtain ⟨hm₃, hrd₃, hwr₃, pub₃, hx₃, hy₃⟩ := hk₃
    rw [WP.block_append_iff]
    have hH : ∀ k : Nat, (hk : k < 8) → s₃.mem.readW (st s₀ + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 32 =
        (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1))[k] :=
      fun k hk => by rw [← hM.state, stateAt_get _ _ hk, hm₃, hm₂]
    have hrdi₃ : s₃.gpr .rdi = st s₀ := by rw [pub₃ .rdi (by decide), pub₂ .rdi (by decide)]; exact hM.rdi
    have hrd₃' : s₃.rd = s₀.rd := by rw [hrd₃, hrd₂]; exact hM.rd
    have hwr₃' : s₃.wr = s₀.wr := by rw [hwr₃, hwr₂]; exact hM.wr
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.addState_ok hp _ _ (Vars.vars8 hv₃) hrdi₃ hrd₃' hwr₃' hH)
      fun s₄ ⟨hm₄, _, pub₄, hrd₄, hwr₄, hx₄, hy₄⟩ => ?_
    have pub₄' : ∀ r ∈ VG.Proof.Sha256.X86_64.Avx2.pubRegs, s₄.gpr r = s₁.gpr r := fun r hr => by rw [pub₄ r hr, pub₃ r hr, pub₂ r hr]
    have hfw : Frame [stR s₀] s₃.mem s₄.mem := by
      rw [hm₄]; exact frame_writeState (Frame.refl _ _) _
    have hc₄ : VG.Proof.Sha256.X86_64.Avx2.Common s₀ (i + 2) s₄ := by
      refine ⟨by rw [pub₄' .rdi (by decide)]; exact hM.rdi, by rw [pub₄' .rcx (by decide)]; exact hM.rcx,
        by rw [pub₄' .rsp (by decide)]; exact hM.rsp, by rw [hrd₄, hrd₃, hrd₂]; exact hM.rd,
        by rw [hwr₄, hwr₃, hwr₂]; exact hM.wr, ?_, ?_, ?_, ?_⟩
      · refine hM.frame.trans ?_
        rw [← hm₂, ← hm₃]
        exact hfw.sub fun r hr => ⟨stR s₀, by simp, by simp at hr; subst hr; exact fun _ h => h⟩
      · rw [hm₄, stateAt_writeState, show i + 2 = i + 1 + 1 by omega, compressBlocks_succ _ _ _ (i + 1)]; rfl
      · refine VG.Proof.Sha256.X86_64.Avx2.saved_frame hp ?_ (.inr hfw)
        rw [hm₃, hm₂]; exact hM.saved
      · rw [VG.Proof.Sha256.X86_64.Avx2.Masks, hx₄, hy₄, hx₃, hy₃, hx₂, hy₂]; exact hM.masks
    refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.adv_common hc₄ 128 2) fun s₅ ⟨hc, he, hrsi, hrdx⟩ => ?_
    have hrdx' : s₄.gpr .rdx - BitVec.signExtend 64 (2 : BitVec 32) = BitVec.ofNat 64 (nb s₀ - (i + 2)) := by
      rw [pub₄' .rdx (by decide), hM.rdx, VG.Proof.Sha256.X86_64.Avx2.e2, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
    rw [hrdx'] at he hrdx
    refine VG.Proof.Sha256.X86_64.Avx2.exit_or_next hp (by omega) (by omega) hc ?_ hrdx he
    rw [hrsi, pub₄' .rsi (by decide), hM.rsi, VG.Proof.Sha256.X86_64.Avx2.e128]; simp only [blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, ← BitVec.ofNat_add,
      show 64 * (i + 2) = 64 * i + 128 by omega]

/-! ## The prologue and the epilogue -/

theorem saveMem_saved {s₀ : State} : VG.Proof.Sha256.X86_64.Avx2.Saved s₀ (VG.Proof.Sha256.X86_64.Avx2.saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame {s₀ : State} : Frame [scrR s₀] s₀.mem (VG.Proof.Sha256.X86_64.Avx2.saveMem s₀) :=
  Spill.saveMem_frame_base _ _ _ _ (fun p hp => by have := VG.Proof.Sha256.X86_64.Avx2.saved_bound p hp; omega) (by decide)

theorem common_zero {s₀ : State} (hp : Pre s₀) {s₁ : State} (hg : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = VG.Proof.Sha256.X86_64.Avx2.saveMem s₀) (hk : VG.Proof.Sha256.X86_64.Avx2.Masks s₁) :
    VG.Proof.Sha256.X86_64.Avx2.Common s₀ 0 s₁ := by
  refine ⟨hg _ (by decide), hg _ (by decide), hg _ (by decide), hrd, hwr, ?_, ?_,
    by rw [hm]; exact VG.Proof.Sha256.X86_64.Avx2.saveMem_saved, hk⟩
  · rw [hm]; exact saveMem_frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [hm]
    apply stateAt_eq
    intro k hk
    rw [saveMem_frame.readW (contains_offset' (off := 4 * k) (len := 32) (by omega) (by omega))
      (by simpa using hp.st_scr) (by decide), ← stateAt_get _ _ hk]
    rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (hc : VG.Proof.Sha256.X86_64.Avx2.Common s₀ (nb s₀) s) :
    WP isa (.block (restore ++ ([.vop .vzeroupper] : List Instr))) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hc.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
  refine Spill.restore_then .rcx saved s₀.gpr (by decide) (fun p hp' => ?_)
    (by rw [hc.rcx]; exact hc.saved) ?_
  · have := VG.Proof.Sha256.X86_64.Avx2.saved_bound p hp'
    rw [hc.rcx, hc.rd, hc.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have hm := (Spill.restoreState_mem s₀.gpr s saved).1
  have hg := Spill.restoreState_calleeSaved (l := saved) (by decide) hc.rsp
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left']
  exact ⟨⟨hg, by rw [hm]; exact hret⟩, by show stateAt _ _ = _; rw [hm]; exact hc.state⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Sha256.X86_64.Avx2.prologue_ok hp) fun s₁ ⟨hg, hrd, hwr, hm, hzf, hk⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha256.X86_64.Avx2.Common s₀ (nb s₀)) ?_ fun s₂ hc => VG.Proof.Sha256.X86_64.Avx2.restore_ok hp hc)
  have hc₀ := VG.Proof.Sha256.X86_64.Avx2.common_zero hp hg hrd hwr hm hk
  refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ VG.Proof.Sha256.X86_64.Avx2.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Sha256.X86_64.Avx2.Common s₀ (nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Sha256.X86_64.Avx2.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, i', hii, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - i', by omega, i', rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Sha256.X86_64.Avx2.LInv s₀ 0 s₁ :=
      { hc₀ with
        rsi := by rw [hg _ (by decide)]; simp [blkAddr]
        rdx := by rw [hg _ (by decide)]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem compress_verified :
    Verified X86_64.target Impl.Sha256.X86_64.Avx2.compress Proof.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, (Proof.Sha256.X86_64.compress_verified).2.2⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.Sha256.X86_64.Avx2.correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.Sha256.X86_64.Avx2

end
