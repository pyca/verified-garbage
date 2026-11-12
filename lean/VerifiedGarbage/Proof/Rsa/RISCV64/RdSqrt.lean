module

public import VerifiedGarbage.Proof.Rsa.RISCV64.RdOps
public import VerifiedGarbage.Proof.Rsa.RISCV64.RdStage2
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Bignum.SqrtRem
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2Words
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.RdShift
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.WordStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

-- separate module: the square root by words, which only `RdCorrect` imports, is the largest piece of the function

/-!
# The square root by words of `vg_rsa_recover_primes_det` on RISC-V

`RecoverDet.sqrt` (`Impl/Rsa/RISCV64/RecoverDet.lean`) on the wide view
(`W = W2 w` words): `[aSy] := ⌊√X⌋` modulo `2^(64 w)` for the radicand
`X = [wR]`, and `sOk5 := [⌊√X⌋² = X]`, against `VG.Spec.Rsa.isqrt` through
`Proof/Bignum/SqrtRem.lean`:

* `norm_ok`: `X` shifted up by an even `2 c` bits, `c` saved, until its top
  two bits are not both zero (and whether `X = 0`), its top nonzero word read
  by a scan of every word (`topW_ok`), not at its secret index;
* `first_ok`: the first digit `s₀ = ⌊√T⌋` of the top two words `T`, by 64
  steps of `pairStep` (`pair_val`, `RecoverDet.sqrtInv_step`), the remainder
  `T - s₀²`, and the reciprocal `⌊(2^128 - 1) / s₀⌋ - 2^64` of the normalized
  `s₀ ≥ 2^63`;
* `digit_ok`: a digit, estimated from the remainder's top words and the
  reciprocal (`est_bounds`), at most three above the true one
  (`SqrtRem.div_le_digit_succ`), `(2 S β + q) q` subtracted and corrected
  back while the remainder is negative (`correct_ok`), so the digit
  (`digit_isqrt`, `SqrtRem.step_inv`);
* `digits_ok`: the `k - 1` digits after the first keep `DV`, the root and
  remainder of `X`'s top `2 m` words;
* `sqrt_ok`: the root of the normalized `X`, shifted down by `c`, is `X`'s
  (`SqrtRem.norm_sqrt`), and the remainder zero exactly where `X` is a square
  (`SqrtRem.norm_square`); `X = 0` selects the zero root.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Keys

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Loops
open VG.Proof.Rsa.RecoverDet (sqrtStep SqrtInv sqrtInv_step)
open VG.Spec.Rsa (isqrt)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.Rsa.RISCV64.Keys (mov ptr seqs eqS copy sel)
open VG.Impl.Rsa.RISCV64.RecoverDet (pairStep msBody corBody fHead fMid first wR wSN wTmp wDig dLoad dEst dPtr
  dSq dTop dNext cHead cTail correct digit dsHead digits nTop nShift norm sBb sOk5 sqrt saveDiv restDiv aSy aZero
  ctxw shrBy)
open VG.Impl.Bignum.RISCV64.Precompute (recipHead divBit lzStep)

/-! ## Two words -/

/-- The value of two words, high and low. -/
abbrev v2 (h l : BitVec 64) : Nat := h.toNat * 2 ^ 64 + l.toNat

/-- `1` if `x < y`, by `sltu`. -/
abbrev bor (x y : BitVec 64) : BitVec 64 := if x < y then 1 else 0

theorem bor_toNat (x y : BitVec 64) : (bor x y).toNat = if x.toNat < y.toNat then 1 else 0 := by
  unfold bor; by_cases h : x < y
  · have h' : x.toNat < y.toNat := BitVec.lt_def.mp h
    simp only [h, h', ↓reduceIte]; rfl
  · have h' : ¬ x.toNat < y.toNat := fun h' => h (BitVec.lt_def.mpr h')
    simp only [h, h', ↓reduceIte]; rfl

/-- `h` shifted up by two bits, with `l`'s top two bits in. -/
abbrev sh2 (h l : BitVec 64) : BitVec 64 := h <<< 2 ||| l >>> 62

theorem sq_and_shl_small (x c : BitVec 64) (k : Nat) (hc : c.toNat < 2 ^ k) : (x <<< k) &&& c = 0 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft]
  by_cases h : i < k
  · simp [h]
  · have : c[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

theorem sh2_toNat (h l : BitVec 64) : (sh2 h l).toNat = 4 * h.toNat % 2 ^ 64 + l.toNat / 2 ^ 62 := by
  have hl := l.isLt
  have h1 : (h <<< 2).toNat = 4 * h.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h2 : (l >>> 62).toNat = l.toNat / 2 ^ 62 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small h (l >>> 62) 2 (by rw [h2]; omega)
  unfold sh2
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega

/-- Two words shifted up by two bits, the next word's top two bits in. -/
theorem v2_sh2 (a b c : BitVec 64) : v2 (sh2 a b) (sh2 b c) = (4 * v2 a b + c.toNat / 2 ^ 62) % 2 ^ 128 := by
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
  simp only [v2, sh2_toNat]
  omega

theorem ite10_eq_one (p : Prop) [Decidable p] : ((if p then (1 : Nat) else 0) = 1) ↔ p := by
  by_cases h : p
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, iff_false]; omega

theorem ite10_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    (if p then (1 : Nat) else 0) = if q then 1 else 0 := by
  by_cases hp : p
  · simp only [hp, h.mp hp, ↓reduceIte]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp only [hp, hq, ↓reduceIte]

/-- Two words less two words: the borrow out, and the difference where there is none. -/
theorem sub2_val (xh xl yh yl : BitVec 64) :
    ((bor xh yh ||| bor (xh - yh) (bor xl yl)).toNat = if v2 xh xl < v2 yh yl then 1 else 0) ∧
      (v2 yh yl ≤ v2 xh xl → v2 (xh - yh - bor xl yl) (xl - yl) = v2 xh xl - v2 yh yl) := by
  have hxh := xh.isLt; have hxl := xl.isLt; have hyh := yh.isLt; have hyl := yl.isLt
  have e1 := bor_toNat xh yh
  have e2 := bor_toNat (xh - yh) (bor xl yl)
  have e3 := bor_toNat xl yl
  have b1 : (bor xh yh).toNat ≤ 1 := by rw [e1]; split <;> omega
  have b2 : (bor (xh - yh) (bor xl yl)).toNat ≤ 1 := by rw [e2]; split <;> omega
  have hor : (bor xh yh ||| bor (xh - yh) (bor xl yl)).toNat =
      if (bor xh yh).toNat = 1 ∨ (bor (xh - yh) (bor xl yl)).toNat = 1 then 1 else 0 := by
    have : ∀ a b : BitVec 64, a.toNat ≤ 1 → b.toNat ≤ 1 →
        (a ||| b).toNat = if a.toNat = 1 ∨ b.toNat = 1 then 1 else 0 := by
      intro a b ha hb
      have ea : a = 0#64 ∨ a = 1#64 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with h | h
        · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      have eb : b = 0#64 ∨ b = 1#64 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
        · exact .inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
        · exact .inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rcases ea with rfl | rfl <;> rcases eb with rfl | rfl <;> decide
    exact this _ _ b1 b2
  have s1 : (xh - yh).toNat = (2 ^ 64 - yh.toNat + xh.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have s2 : (xl - yl).toNat = (2 ^ 64 - yl.toNat + xl.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have s3 : (xh - yh - bor xl yl).toNat =
      (2 ^ 64 - (bor xl yl).toNat + (xh - yh).toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have b3 : (bor xl yl).toNat ≤ 1 := by rw [e3]; split <;> omega
  constructor
  · rw [hor, e1, e2, s1, e3]
    simp only [v2]
    apply ite10_congr
    rw [ite10_eq_one, ite10_eq_one]
    by_cases c1 : xl.toNat < yl.toNat <;> simp only [c1, ↓reduceIte] <;> omega
  · intro hle
    simp only [v2] at hle ⊢
    rw [s3, s2, s1, e3]
    by_cases c1 : xl.toNat < yl.toNat <;> simp only [c1, ↓reduceIte] <;> omega

/-- A choice by a mask `b - 1`, `b` a bit: `x` where `b = 1`, `d` where `b = 0`. -/
theorem sel_mask (x d b : BitVec 64) (hb : b.toNat ≤ 1) :
    x ^^^ ((d ^^^ x) &&& (b - 1#64)) = if b.toNat = 0 then d else x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
  · have : b = 0#64 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    subst this
    simp only [h, ↓reduceIte, BitVec.zero_sub, BitVec.neg_one_eq_allOnes, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x d, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · have : b = 1#64 := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    subst this
    simp [h]

/-! ## A bit pair of the first digit -/

/-- `pairStep`'s borrow: `1` where the remainder is below `4 y + 1`. -/
abbrev pB (a2 a4 a5 s0 : BitVec 64) : BitVec 64 :=
  bor (sh2 a4 a5) (s0 <<< 1 >>> 63) |||
    bor (sh2 a4 a5 - s0 <<< 1 >>> 63) (bor (sh2 a5 a2) (s0 <<< 1 <<< 1 ||| 1#64))

/-- `pairStep`'s new remainder, high and low word. -/
abbrev pR4 (a2 a4 a5 s0 : BitVec 64) : BitVec 64 :=
  sh2 a4 a5 ^^^ ((sh2 a4 a5 - s0 <<< 1 >>> 63 - bor (sh2 a5 a2) (s0 <<< 1 <<< 1 ||| 1#64) ^^^ sh2 a4 a5) &&&
    (pB a2 a4 a5 s0 - 1#64))
abbrev pR5 (a2 a4 a5 s0 : BitVec 64) : BitVec 64 :=
  sh2 a5 a2 ^^^ ((sh2 a5 a2 - (s0 <<< 1 <<< 1 ||| 1#64) ^^^ sh2 a5 a2) &&& (pB a2 a4 a5 s0 - 1#64))

/-- `4 y + 1` for `y < 2^63`, as two words. -/
theorem trial_v2 (s0 : BitVec 64) (hs : s0.toNat < 2 ^ 63) :
    v2 (s0 <<< 1 >>> 63) (s0 <<< 1 <<< 1 ||| 1#64) = 4 * s0.toNat + 1 := by
  have e1 : (s0 <<< 1).toNat = 2 * s0.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have e2 : (s0 <<< 1 >>> 63).toNat = 2 * s0.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e1]
  have e3 : (s0 <<< 1 <<< 1).toNat = 4 * s0.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, e1]; omega
  have hd := sq_and_shl_small (s0 <<< 1) 1#64 1 (by decide)
  have e4 : (s0 <<< 1 <<< 1 ||| 1#64).toNat = 4 * s0.toNat % 2 ^ 64 + 1 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, e3]
    have : (1#64).toNat = 1 := rfl
    rw [this]; omega
  simp only [v2, e2, e4]
  omega

theorem x4_val (a2 a3 : BitVec 64) : v2 (sh2 a2 a3) (a3 <<< 2) = 4 * v2 a2 a3 % 2 ^ 128 := by
  have ha2 := a2.isLt; have ha3 := a3.isLt
  have e : (a3 <<< 2).toNat = 4 * a3.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  simp only [v2, sh2_toNat, e]
  omega

/-- `sqrtStep 128 128`'s remainder before the trial subtraction, on two-word values. -/
theorem pair_r (a2 a3 : BitVec 64) (R : Nat) :
    2 * (2 * R % 2 ^ 128 + 2 * v2 a2 a3 / 2 ^ 128) % 2 ^ 128 + 2 * (2 * v2 a2 a3 % 2 ^ 128) / 2 ^ 128 =
      (4 * R + a2.toNat / 2 ^ 62) % 2 ^ 128 := by
  have ha2 := a2.isLt; have ha3 := a3.isLt
  simp only [v2]; omega

theorem pair_x (X : Nat) : 2 * (2 * X % 2 ^ 128) % 2 ^ 128 = 4 * X % 2 ^ 128 := by omega

theorem pair_t {y : Nat} (hy : y < 2 ^ 63) : 2 * (2 * y) % 2 ^ 128 + 1 = 4 * y + 1 := by omega

theorem pair_y {y : Nat} (hy : y < 2 ^ 63) : 2 * y % 2 ^ 128 = 2 * y := by omega

theorem shl1_toNat {y : BitVec 64} (hy : y.toNat < 2 ^ 63) : (y <<< 1).toNat = 2 * y.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

/-- A step of `pairStep` is `sqrtStep 128 128` on the top two words `a2:a3`, the
remainder `a4:a5` and the root `s0 < 2^63`. -/
theorem pair_val (a2 a3 a4 a5 s0 : BitVec 64) (hs : s0.toNat < 2 ^ 63) :
    sqrtStep 128 128 (v2 a2 a3, v2 a4 a5, s0.toNat) =
      (v2 (sh2 a2 a3) (a3 <<< 2), v2 (pR4 a2 a4 a5 s0) (pR5 a2 a4 a5 s0),
        (s0 <<< 1 ||| (pB a2 a4 a5 s0 ^^^ 1#64)).toNat) := by
  have ha2 := a2.isLt; have ha3 := a3.isLt
  have tv := trial_v2 s0 hs
  obtain ⟨sb, sd⟩ := sub2_val (sh2 a4 a5) (sh2 a5 a2) (s0 <<< 1 >>> 63) (s0 <<< 1 <<< 1 ||| 1#64)
  rw [tv] at sb sd
  have r4 : v2 (sh2 a4 a5) (sh2 a5 a2) = (4 * v2 a4 a5 + a2.toNat / 2 ^ 62) % 2 ^ 128 := v2_sh2 a4 a5 a2
  have e1 : (s0 <<< 1).toNat = 2 * s0.toNat := shl1_toNat hs
  have pb1 : (pB a2 a4 a5 s0).toNat ≤ 1 := by
    show (bor _ _ ||| bor _ _).toNat ≤ 1
    rw [sb]; split <;> omega
  have hd := sq_and_shl_small s0 (pB a2 a4 a5 s0 ^^^ 1#64) 1 (by
    have : (pB a2 a4 a5 s0 ^^^ 1#64).toNat ≤ 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp pb1 with h | h
      · rw [show pB a2 a4 a5 s0 = 0#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]; decide
      · rw [show pB a2 a4 a5 s0 = 1#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]; decide
    omega)
  have rt : (s0 <<< 1 ||| (pB a2 a4 a5 s0 ^^^ 1#64)).toNat =
      2 * s0.toNat + if (pB a2 a4 a5 s0).toNat = 0 then 1 else 0 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, e1]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp pb1 with h | h
    · simp only [h, ↓reduceIte]
      rw [show pB a2 a4 a5 s0 = 0#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]
      have : (0#64 ^^^ 1#64).toNat = 1 := rfl
      rw [this]; omega
    · simp only [h, Nat.one_ne_zero, ↓reduceIte]
      rw [show pB a2 a4 a5 s0 = 1#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]
      have : (1#64 ^^^ 1#64).toNat = 0 := rfl
      rw [this]; omega
  have m4 : pR4 a2 a4 a5 s0 = if (pB a2 a4 a5 s0).toNat = 0 then
      sh2 a4 a5 - s0 <<< 1 >>> 63 - bor (sh2 a5 a2) (s0 <<< 1 <<< 1 ||| 1#64) else sh2 a4 a5 :=
    sel_mask _ _ _ pb1
  have m5 : pR5 a2 a4 a5 s0 = if (pB a2 a4 a5 s0).toNat = 0 then
      sh2 a5 a2 - (s0 <<< 1 <<< 1 ||| 1#64) else sh2 a5 a2 :=
    sel_mask _ _ _ pb1
  unfold sqrtStep
  simp only [pair_r, pair_x, pair_t hs, pair_y hs, x4_val, rt]
  rw [m4, m5]
  rw [← r4]
  by_cases c : v2 (sh2 a4 a5) (sh2 a5 a2) < 4 * s0.toNat + 1
  · have hb : (pB a2 a4 a5 s0).toNat = 1 := by
      show (bor _ _ ||| bor _ _).toNat = 1; rw [sb]; simp only [c, ↓reduceIte]
    simp only [c, ↓reduceIte, hb, Nat.one_ne_zero, Nat.add_zero]
  · have hb : (pB a2 a4 a5 s0).toNat = 0 := by
      show (bor _ _ ||| bor _ _).toNat = 0; rw [sb]; simp only [c, ↓reduceIte]
    simp only [c, ↓reduceIte, hb]
    rw [sd (by omega)]

/-! ## The words of `2 s` -/

/-- A word of `2 s`, from `s`'s word `x` and the one below, `p`. -/
abbrev dbl (x p : BitVec 64) : BitVec 64 := x <<< 1 ||| p >>> 63

theorem dbl_toNat (x p : BitVec 64) : (dbl x p).toNat = 2 * x.toNat % 2 ^ 64 + p.toNat / 2 ^ 63 := by
  have hp := p.isLt
  have h1 : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have h2 : (p >>> 63).toNat = p.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small x (p >>> 63) 1 (by rw [h2]; omega)
  unfold dbl
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega

/-- The top bit of a word. -/
theorem shr63_toNat' (x : BitVec 64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Multiply-subtract and masked add, a word -/

/-- `msBody`'s word: `x - (q d + c)`, and the carry `⌊q d / 2^64⌋` plus the two borrows. -/
theorem msw_arith (q d x c : BitVec 64) :
    (x - (q * d + c)).toNat + q.toNat * d.toNat + c.toNat =
      x.toNat + 2 ^ 64 * (BitVec.ofNat 64 (q.toNat * d.toNat / 2 ^ 64) + bor (q * d + c) c +
        bor x (q * d + c)).toNat := by
  have hq := q.isLt; have hd := d.isLt; have hx := x.isLt; have hc := c.isLt
  have hP : q.toNat * d.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have l1 : (q * d + c).toNat = (q.toNat * d.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul]
  have b1 := bor_toNat (q * d + c) c
  have b2 := bor_toNat x (q * d + c)
  have hb1 : (bor (q * d + c) c).toNat ≤ 1 := by rw [b1]; split <;> omega
  have hb2 : (bor x (q * d + c)).toNat ≤ 1 := by rw [b2]; split <;> omega
  have hi : (BitVec.ofNat 64 (q.toNat * d.toNat / 2 ^ 64)).toNat = q.toNat * d.toNat / 2 ^ 64 := by
    rw [BitVec.toNat_ofNat]; omega
  -- The carry out does not wrap: `⌊q d / 2^64⌋ + 2 ≤ 2^64` but where both borrows are set.
  have e : (BitVec.ofNat 64 (q.toNat * d.toNat / 2 ^ 64) + bor (q * d + c) c + bor x (q * d + c)).toNat =
      q.toNat * d.toNat / 2 ^ 64 + (bor (q * d + c) c).toNat + (bor x (q * d + c)).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_add, hi]
    rw [b1, b2, l1]
    by_cases c1 : (q.toNat * d.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 < c.toNat <;>
      by_cases c2 : x.toNat < (q.toNat * d.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 <;>
      simp only [c1, c2, ↓reduceIte] <;> omega
  have s1 : (x - (q * d + c)).toNat = (2 ^ 64 - (q * d + c).toNat + x.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  rw [e, s1, b1, b2, l1]
  by_cases c1 : (q.toNat * d.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 < c.toNat <;>
    by_cases c2 : x.toNat < (q.toNat * d.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 <;>
    simp only [c1, c2, ↓reduceIte] <;> omega

/-- `corBody`'s word: `x + c + e`, the carry the two carries. -/
theorem corw_arith (x c e : BitVec 64) :
    (x + c + e).toNat + 2 ^ 64 * (bor (x + c) c + bor (x + c + e) e).toNat = x.toNat + c.toNat + e.toNat := by
  have hx := x.isLt; have hc := c.isLt; have he := e.isLt
  have b1 := bor_toNat (x + c) c
  have b2 := bor_toNat (x + c + e) e
  have a1 : (x + c).toNat = (x.toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have a2 : (x + c + e).toNat = ((x + c).toNat + e.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have s : (bor (x + c) c + bor (x + c + e) e).toNat = (bor (x + c) c).toNat + (bor (x + c + e) e).toNat := by
    rw [BitVec.toNat_add, b1, b2]; split <;> split <;> omega
  rw [s, b1, b2, a2, a1]
  by_cases c1 : (x.toNat + c.toNat) % 2 ^ 64 < c.toNat <;>
    by_cases c2 : ((x.toNat + c.toNat) % 2 ^ 64 + e.toNat) % 2 ^ 64 < e.toNat <;>
    simp only [c1, c2, ↓reduceIte] <;> omega

/-- A word under the mask `0 - b`, `b` a bit. -/
theorem and_mask_toNat (x b : BitVec 64) (hb : b.toNat ≤ 1) : (x &&& (0#64 - b)).toNat = b.toNat * x.toNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h | h
  · rw [show b = 0#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]; simp
  · rw [show b = 1#64 from BitVec.eq_of_toNat_eq (by rw [h]; rfl)]
    rw [show (0#64 - 1#64) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]; simp

/-! ## The loops of a digit -/

/-- The registers `msBody`'s loop writes. -/
abbrev msRegs : List Reg := [.t2, .t3, .t4, .t5, .a0, .a4, .a5, .a6, .a7]

/-- `countLoop .a7 msBody`: the `n` words at `a5` less `q (2 [s]) + c`, `q` in `s8`, `c` in `a4`, for
the `n` words `[s]` at `a6` and `t2 = 0` (no bit below): the carry out in `a4`, and the bit of `2 [s]`
past its `n` words, from `t2`, its top word. -/
theorem msLoop_ok {s : State} {B : Addr} {Z dO dS n : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dO) (h6 : s.gpr .a6 = off B dS) (h7 : s.gpr .a7 = BitVec.ofNat 64 n)
    (h2 : s.gpr .t2 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hS8 : dS % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hS : dS + 8 * n ≤ Z) (hd : dS + 8 * n ≤ dO ∨ dO + 8 * n ≤ dS) :
    WP isa (countLoop .a7 msBody) s fun t =>
      wordsVal t.mem B dO n + (s.gpr .s8).toNat * (2 * wordsVal s.mem B dS n) + (s.gpr .a4).toNat =
        wordsVal s.mem B dO n + 2 ^ (64 * n) * ((t.gpr .a4).toNat + (s.gpr .s8).toNat * ((t.gpr .t2).toNat / 2 ^ 63)) ∧
      t.gpr .t2 = word s.mem B (dS + 8 * (n - 1)) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep msRegs s t ∧ t.gpr .a5 = off B (dO + 8 * n) ∧
      t.gpr .a6 = off B (dS + 8 * n) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .a5 = off B (dO + 8 * i) ∧ t.gpr .a6 = off B (dS + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + (s.gpr .s8).toNat * (2 * wordsVal s.mem B dS i) + (s.gpr .a4).toNat =
        wordsVal s.mem B dO i + 2 ^ (64 * i) * ((t.gpr .a4).toNat + (s.gpr .s8).toNat * ((t.gpr .t2).toNat / 2 ^ 63)) ∧
      (0 < i → t.gpr .t2 = word s.mem B (dS + 8 * (i - 1))) ∧ Keep msRegs s t
  refine WP.mono (wp_countdown (body := .block (msBody ++ ([.addi .a7 .a7 (-1)] : List Instr)))
    (cnt := .a7) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jt2, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _, by simp [wordsVal, h2], fun h => absurd h (by decide),
      Keep.refl _ _⟩ h7)
    fun t ⟨j5, j6, jout, jeq, jt2, jk⟩ => ⟨jeq, jt2 (by omega), jout, jk, j5, j6⟩
  have hs' := hs.congr jk.2.2
  have h8 : t.gpr .s8 = s.gpr .s8 := jk.gpr (by decide)
  have hst : WP isa (.block (msBody ++ ([.addi .a7 .a7 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .a5 = off B (dO + 8 * i + 8) ∧ t'.gpr .a6 = off B (dS + 8 * i + 8) ∧
        t'.gpr .a7 = t.gpr .a7 - BitVec.ofNat 64 1 ∧ t'.gpr .t2 = word t.mem B (dS + 8 * i) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) - (t.gpr .s8 * dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) + t.gpr .a4)) ∧
        t'.gpr .a4 = BitVec.ofNat 64 ((t.gpr .s8).toNat * (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2)).toNat / 2 ^ 64) +
          bor (t.gpr .s8 * dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) + t.gpr .a4) (t.gpr .a4) +
          bor (word t.mem B (dO + 8 * i)) (t.gpr .s8 * dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) + t.gpr .a4)) ∧
      Keep msRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [msBody, mov, add_ofNat_zero', j5, j6, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dS + 8 * i + 8 ≤ Z by omega_arith), hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l2, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, fun _ => ?_, Keep.trans' jk lk⟩, l7⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wx : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := msw_arith (t.gpr .s8) (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2)) (word t.mem B (dO + 8 * i))
      (t.gpr .a4)
    have dv := dbl_toNat (word t.mem B (dS + 8 * i)) (t.gpr .t2)
    rw [← l4] at k
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dO i,
      wordsVal_succ_top s.mem B dS i, l2, Nat.mul_succ, Nat.pow_add]
    rw [wo, wx, h8] at k
    rw [wx] at dv
    rw [wo, wx, h8]
    have hx := (word s.mem B (dS + 8 * i)).isLt
    generalize (word s.mem B (dS + 8 * i)).toNat = X at *
    generalize (t.gpr .t2).toNat / 2 ^ 63 = tb at *
    generalize (dbl (word s.mem B (dS + 8 * i)) (t.gpr .t2)).toNat = D at *
    generalize (s.gpr .s8).toNat = q at *
    generalize (word s.mem B (dO + 8 * i)).toNat = xo at *
    generalize (word s.mem B (dO + 8 * i) - (s.gpr .s8 * dbl (word s.mem B (dS + 8 * i)) (t.gpr .t2) + t.gpr .a4)).toNat = x' at *
    generalize (t'.gpr .a4).toNat = c' at *
    generalize (t.gpr .a4).toNat = c at *
    generalize 2 ^ (64 * i) = P at *
    -- `2 X = D - tb + 2^64 ⌊X / 2^63⌋`.
    have e2 : 2 * X + tb = D + 2 ^ 64 * (X / 2 ^ 63) := by omega
    have e3 : q * (2 * X) + q * tb = q * D + 2 ^ 64 * (q * (X / 2 ^ 63)) := by
      rw [← Nat.mul_add, e2, Nat.mul_add, Nat.mul_left_comm]
    grind
  · rw [l2, show i + 1 - 1 = i by omega]
    exact jout.word (by omega_arith) (by omega_arith)

/-- The registers `corBody`'s loop writes. -/
abbrev corRegs : List Reg := [.t2, .t4, .t5, .t6, .a4, .a5, .a6, .a7]

/-- `countLoop .a7 corBody`: the `n` words at `a5` plus `b (2 [s]) + c`, `b` a bit (`t3 = 0 - b`), `c`
in `a4`, for the `n` words `[s]` at `a6` and `t2 = 0`: the carry out in `a4`, and the bit of `2 [s]`
past its `n` words, from `t2`, its top word. -/
theorem corLoop_ok {s : State} {B : Addr} {Z dO dS n : Nat} {b : BitVec 64} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dO) (h6 : s.gpr .a6 = off B dS) (h7 : s.gpr .a7 = BitVec.ofNat 64 n)
    (h2 : s.gpr .t2 = 0) (h3 : s.gpr .t3 = 0#64 - b) (hb : b.toNat ≤ 1)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 32) (hO8 : dO % 8 = 0) (hS8 : dS % 8 = 0)
    (hO : dO + 8 * n ≤ Z) (hS : dS + 8 * n ≤ Z) (hd : dS + 8 * n ≤ dO ∨ dO + 8 * n ≤ dS) :
    WP isa (countLoop .a7 corBody) s fun t =>
      wordsVal t.mem B dO n + 2 ^ (64 * n) * ((t.gpr .a4).toNat + b.toNat * ((t.gpr .t2).toNat / 2 ^ 63)) =
        wordsVal s.mem B dO n + b.toNat * (2 * wordsVal s.mem B dS n) + (s.gpr .a4).toNat ∧
      t.gpr .t2 = word s.mem B (dS + 8 * (n - 1)) ∧
      Outside B dO (8 * n) s.mem t.mem ∧ Keep corRegs s t ∧ t.gpr .a5 = off B (dO + 8 * n) ∧
      t.gpr .a6 = off B (dS + 8 * n) := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .a5 = off B (dO + 8 * i) ∧ t.gpr .a6 = off B (dS + 8 * i) ∧ Outside B dO (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dO i + 2 ^ (64 * i) * ((t.gpr .a4).toNat + b.toNat * ((t.gpr .t2).toNat / 2 ^ 63)) =
        wordsVal s.mem B dO i + b.toNat * (2 * wordsVal s.mem B dS i) + (s.gpr .a4).toNat ∧
      (0 < i → t.gpr .t2 = word s.mem B (dS + 8 * (i - 1))) ∧ Keep corRegs s t
  refine WP.mono (wp_countdown (body := .block (corBody ++ ([.addi .a7 .a7 (-1)] : List Instr)))
    (cnt := .a7) (N := n) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j5, j6, jout, jeq, jt2, jk⟩ hc => ?_)
    ⟨by rw [h5]; rfl, by rw [h6]; rfl, Outside.refl _ _ _ _, by simp [wordsVal, h2], fun h => absurd h (by decide),
      Keep.refl _ _⟩ h7)
    fun t ⟨j5, j6, jout, jeq, jt2, jk⟩ => ⟨jeq, jt2 (by omega), jout, jk, j5, j6⟩
  have hs' := hs.congr jk.2.2
  have t3 : t.gpr .t3 = 0#64 - b := (jk.gpr (by decide)).trans h3
  have hst : WP isa (.block (corBody ++ ([.addi .a7 .a7 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .a5 = off B (dO + 8 * i + 8) ∧ t'.gpr .a6 = off B (dS + 8 * i + 8) ∧
        t'.gpr .a7 = t.gpr .a7 - BitVec.ofNat 64 1 ∧ t'.gpr .t2 = word t.mem B (dS + 8 * i) ∧
        t'.mem = t.mem.writeW (off B (dO + 8 * i))
          (word t.mem B (dO + 8 * i) + t.gpr .a4 + (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) &&& (0#64 - b))) ∧
        t'.gpr .a4 = bor (word t.mem B (dO + 8 * i) + t.gpr .a4) (t.gpr .a4) +
          bor (word t.mem B (dO + 8 * i) + t.gpr .a4 + (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) &&& (0#64 - b)))
            (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) &&& (0#64 - b))) ∧
      Keep corRegs t t' := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [corBody, mov, add_ofNat_zero', j5, j6, t3, hs'.ld (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.ld (show dS + 8 * i + 8 ≤ Z by omega_arith), hs'.st (show dO + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dO + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hs'.al8 (show dS + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l5, l6, l7, l2, lm, l4⟩, lk⟩ => ⟨⟨?_, ?_, ?_, ?_, fun _ => ?_, Keep.trans' jk lk⟩, l7⟩
  · rw [l5, show dO + 8 * i + 8 = dO + 8 * (i + 1) by omega_arith]
  · rw [l6, show dS + 8 * i + 8 = dS + 8 * (i + 1) by omega_arith]
  · rw [lm]; exact out_step _ jout (by omega_arith)
  · have wo : word t.mem B (dO + 8 * i) = word s.mem B (dO + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have wx : word t.mem B (dS + 8 * i) = word s.mem B (dS + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    have k := corw_arith (word t.mem B (dO + 8 * i)) (t.gpr .a4)
      (dbl (word t.mem B (dS + 8 * i)) (t.gpr .t2) &&& (0#64 - b))
    have dv := dbl_toNat (word t.mem B (dS + 8 * i)) (t.gpr .t2)
    rw [and_mask_toNat _ _ hb, ← l4] at k
    rw [lm, fin64_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dO i,
      wordsVal_succ_top s.mem B dS i, l2, Nat.mul_succ, Nat.pow_add]
    rw [wo, wx] at k
    rw [wx] at dv
    rw [wo, wx]
    have hx := (word s.mem B (dS + 8 * i)).isLt
    generalize (word s.mem B (dS + 8 * i)).toNat = X at *
    generalize (t.gpr .t2).toNat / 2 ^ 63 = tb at *
    generalize (dbl (word s.mem B (dS + 8 * i)) (t.gpr .t2)).toNat = D at *
    generalize b.toNat = M at *
    generalize (word s.mem B (dO + 8 * i)).toNat = xo at *
    generalize (word s.mem B (dO + 8 * i) + t.gpr .a4 +
      (dbl (word s.mem B (dS + 8 * i)) (t.gpr .t2) &&& (0#64 - b))).toNat = x' at *
    generalize (t'.gpr .a4).toNat = c' at *
    generalize (t.gpr .a4).toNat = c at *
    generalize 2 ^ (64 * i) = P at *
    have e2 : 2 * X + tb = D + 2 ^ 64 * (X / 2 ^ 63) := by omega
    have e3 : M * (2 * X) + M * tb = M * D + 2 ^ 64 * (M * (X / 2 ^ 63)) := by
      rw [← Nat.mul_add, e2, Nat.mul_add, Nat.mul_left_comm]
    grind
  · rw [l2, show i + 1 - 1 = i by omega]
    exact jout.word (by omega_arith) (by omega_arith)

/-! ## A digit's estimate -/

open VG.Proof.Bignum.SqrtRem (IsDigit digit_lt digit_le_div)

/-- The estimate `q̂ = min(β - 1, ⌊⌊R / (2 β^m)⌋ / d₀⌋)` of a digit, from the root's top word
`d₀ ≥ β / 2` (`S = d₀ β^(m-1) + …`), is at least the digit and at most three above it. -/
theorem est_bounds {m S R P q d0 : Nat} (hm : 1 ≤ m) (hd0 : S / 2 ^ (64 * (m - 1)) = d0)
    (hd1 : 2 ^ 63 ≤ d0) (hR : R ≤ 2 * S) (hP : P < 2 ^ 64 * 2 ^ 64)
    (hq : IsDigit (2 ^ 64) S (R * (2 ^ 64 * 2 ^ 64) + P) q) :
    q ≤ min (2 ^ 64 - 1) ((R * (2 ^ 64 * 2 ^ 64) + P) / (2 * 2 ^ (64 * m)) / d0) ∧
      min (2 ^ 64 - 1) ((R * (2 ^ 64 * 2 ^ 64) + P) / (2 * 2 ^ (64 * m)) / d0) ≤ q + 3 := by
  obtain ⟨lo, hi⟩ := hq
  have hqβ : q < 2 ^ 64 := digit_lt hR hP lo
  have hM : 2 ^ (64 * m) = 2 ^ (64 * (m - 1)) * 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hM]
  generalize hβ : (2 : Nat) ^ 64 = β at *
  generalize hRb : R * (β * β) + P = Rb at *
  generalize hA : 2 ^ (64 * (m - 1)) = A at *
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_two_pow
  have hβ2 : β = 2 * 2 ^ 63 := by rw [← hβ]; rfl
  -- `d₀ A ≤ S < (d₀ + 1) A`.
  have hS1 : d0 * A ≤ S := by rw [← hd0]; exact Nat.div_mul_le_self S A
  have hS2 : S < (d0 + 1) * A := by
    rw [← hd0, Nat.succ_mul]; exact Nat.lt_div_mul_add (by omega)
  have hS0 : 0 < S := Nat.lt_of_lt_of_le (Nat.mul_pos (by omega) hA1) hS1
  have hD : 0 < 2 * S * β := Nat.mul_pos (Nat.mul_pos (by decide) hS0) (by omega)
  have hE : 0 < 2 * (A * β) * d0 := Nat.mul_pos (Nat.mul_pos (by decide) (Nat.mul_pos hA1 (by omega))) (by omega)
  have hEle : 2 * (A * β) * d0 ≤ 2 * S * β := by
    have e : 2 * (A * β) * d0 = 2 * (d0 * A) * β := by ring
    rw [e]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hS1)
  refine ⟨?_, ?_⟩
  · refine Nat.le_min.mpr ⟨by omega, ?_⟩
    refine Nat.le_trans (digit_le_div hD lo) ?_
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_left hEle hE
  · refine Nat.le_trans (Nat.min_le_right _ _) ?_
    rw [Nat.div_div_eq_div_mul]
    refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hE).mpr ?_)
    -- `Rb < 2 S β (q + 1) + (q + 1)² ≤ 2 (d₀ + 1) A β (q + 1) + β² ≤ 2 A β d₀ (q + 4)`.
    have h1 : Rb < 2 * S * β * (q + 1) + (q + 1) * (q + 1) := by
      have : (2 * S * β + (q + 1)) * (q + 1) = 2 * S * β * (q + 1) + (q + 1) * (q + 1) := by ring
      omega
    have h2 : (q + 1) * (q + 1) ≤ β * β := Nat.mul_le_mul (by omega) (by omega)
    have h3 : 2 * S * β * (q + 1) ≤ 2 * ((d0 + 1) * A) * β * (q + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))
    have h4 : β * β ≤ 2 * (A * β) * 2 ^ 63 := by
      have e : 2 * (A * β) * 2 ^ 63 = A * (β * β) := by rw [hβ2]; ring
      rw [e]; exact Nat.le_mul_of_pos_left _ hA1
    have e1 : (d0 + 1) * (q + 1) = d0 * q + d0 + q + 1 := by ring
    have e2 : d0 * (q + 4) = d0 * q + 4 * d0 := by ring
    have h5 : (d0 + 1) * (q + 1) + 2 ^ 63 ≤ d0 * (q + 4) := by rw [e1, e2]; omega
    have e3 : 2 * ((d0 + 1) * A) * β * (q + 1) + 2 * (A * β) * 2 ^ 63 =
        2 * (A * β) * ((d0 + 1) * (q + 1) + 2 ^ 63) := by ring
    calc Rb < 2 * S * β * (q + 1) + (q + 1) * (q + 1) := h1
      _ ≤ 2 * ((d0 + 1) * A) * β * (q + 1) + β * β := Nat.add_le_add h3 h2
      _ ≤ 2 * ((d0 + 1) * A) * β * (q + 1) + 2 * (A * β) * 2 ^ 63 := Nat.add_le_add_left h4 _
      _ = 2 * (A * β) * ((d0 + 1) * (q + 1) + 2 ^ 63) := e3
      _ ≤ 2 * (A * β) * (d0 * (q + 4)) := Nat.mul_le_mul_left _ h5
      _ = (q + 3).succ * (2 * (A * β) * d0) := by rw [Nat.succ_eq_add_one]; ring

/-! ## A digit and its corrections -/

open VG.Proof.Rsa.RecoverDet (isqrt_sq_le lt_succ_isqrt_sq)

theorem le_isqrt {t x : Nat} (h : t * t ≤ x) : t ≤ isqrt x := by
  refine Nat.le_of_not_lt fun c => ?_
  have := lt_succ_isqrt_sq x
  have : (isqrt x + 1) * (isqrt x + 1) ≤ t * t := Nat.mul_le_mul c c
  omega

/-- The digit after the root `S` of `A`: `isqrt (A β² + P) - S β`. -/
theorem digit_isqrt {β S R A P : Nat} (h : S * S + R = A) :
    IsDigit β S (R * (β * β) + P) (isqrt (A * (β * β) + P) - S * β) := by
  have lo := isqrt_sq_le (A * (β * β) + P)
  have hi := lt_succ_isqrt_sq (A * (β * β) + P)
  have hSb : S * β ≤ isqrt (A * (β * β) + P) := le_isqrt (by
    rw [← h]
    calc S * β * (S * β) = S * S * (β * β) := by ring
      _ ≤ (S * S + R) * (β * β) + P := Nat.le_add_right_of_le (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
  obtain ⟨q, hq⟩ : ∃ q, isqrt (A * (β * β) + P) = S * β + q := ⟨_, (Nat.add_sub_of_le hSb).symm⟩
  rw [hq, Nat.add_sub_cancel_left]
  rw [hq] at lo hi
  have e1 : (S * β + q) * (S * β + q) = S * S * (β * β) + (2 * S * β + q) * q := by ring
  have e2 : (S * β + q + 1) * (S * β + q + 1) = S * S * (β * β) + (2 * S * β + (q + 1)) * (q + 1) := by ring
  have eA : A * (β * β) + P = S * S * (β * β) + (R * (β * β) + P) := by rw [← h]; ring
  rw [e1, eA] at lo
  rw [e2, eA] at hi
  exact ⟨by omega, by omega⟩

/-- `q (2 S β + q)`, what a digit `q` takes off the remainder. -/
abbrev qOf (D q : Nat) : Nat := q * (D + q)

theorem qOf_mono {D x y : Nat} (h : x ≤ y) : qOf D x ≤ qOf D y :=
  Nat.mul_le_mul h (Nat.add_le_add_left h _)

/-- The remainder `Rb - qOf D q̂` over `K` words as `V`, its sign `b`: `V + qOf D q̂ = Rb + b β^K`. -/
def Enc (E D Rb V qh b : Nat) : Prop := V + qOf D qh = Rb + b * E ∧ b ≤ 1

/-- The sign is whether the remainder is negative. -/
theorem Enc.sign {E D Rb V qh b : Nat} (h : Enc E D Rb V qh b) (hV : V < E) :
    b = if Rb < qOf D qh then 1 else 0 := by
  obtain ⟨e, hb⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · rw [Nat.zero_mul, Nat.add_zero] at e
    rw [ite_eq_right (by omega)]
  · rw [Nat.one_mul] at e
    rw [ite_eq_left (by omega)]

/-- A correction: where negative, `2 S β + 2 q̂ - 1` added back, the carry out `c`, and `q̂ - 1`. -/
theorem Enc.correct {E D Rb V V' qh b c : Nat} (h : Enc E D Rb V qh b) (hV : V < E)
    (hQ : qOf D qh < E) (hc : c ≤ 1) (hadd : V' + E * c = V + b * (D + 2 * qh - 1)) :
    Enc E D Rb V' (qh - b) (b * (1 - c)) := by
  obtain ⟨e, hb⟩ := h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero] at e hadd ⊢
    have : c = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
      · exact h0
      · subst h1; omega
    subst this
    exact ⟨by omega, by omega⟩
  · simp only [Nat.one_mul] at e hadd ⊢
    have q1 : 1 ≤ qh := by
      rcases Nat.eq_zero_or_pos qh with h0 | h0
      · subst h0; simp only [qOf, Nat.zero_mul] at e; omega
      · exact h0
    have cs := VG.Proof.Bignum.SqrtRem.correction_step D qh q1
    have hQ' : qOf D qh = qOf D (qh - 1) + (D + 2 * qh - 1) := by simp only [qOf]; rw [Nat.mul_comm, cs, Nat.mul_comm]
    refine ⟨?_, by omega⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h0 | h1
    · subst h0; omega
    · subst h1; omega

/-- From an estimate at most three above the digit, three corrections give the digit. -/
theorem Enc.three {E D Rb V0 V1 V2 V3 q qh b0 c1 c2 c3 : Nat}
    (hq1 : qOf D q ≤ Rb) (hq2 : Rb < qOf D (q + 1)) (hlo : q ≤ qh) (hhi : qh ≤ q + 3)
    (h0 : Enc E D Rb V0 qh b0) (hV0 : V0 < E) (hV1 : V1 < E) (hV2 : V2 < E) (hV3 : V3 < E)
    (hQ : qOf D qh < E) (hc1 : c1 ≤ 1) (hc2 : c2 ≤ 1) (hc3 : c3 ≤ 1)
    (a1 : V1 + E * c1 = V0 + b0 * (D + 2 * qh - 1))
    (a2 : V2 + E * c2 = V1 + b0 * (1 - c1) * (D + 2 * (qh - b0) - 1))
    (a3 : V3 + E * c3 = V2 + b0 * (1 - c1) * (1 - c2) * (D + 2 * (qh - b0 - b0 * (1 - c1)) - 1)) :
    qh - b0 - b0 * (1 - c1) - b0 * (1 - c1) * (1 - c2) = q ∧ b0 * (1 - c1) * (1 - c2) * (1 - c3) = 0 ∧
      V3 = Rb - qOf D q := by
  have mono : ∀ x, q < x → Rb < qOf D x := fun x hx => Nat.lt_of_lt_of_le hq2 (qOf_mono hx)
  have mono' : ∀ x, x ≤ q → qOf D x ≤ Rb := fun x hx => Nat.le_trans (qOf_mono hx) hq1
  have hQle : ∀ x, x ≤ qh → qOf D x < E := fun x hx => Nat.lt_of_le_of_lt (qOf_mono hx) hQ
  have e1 := h0.correct hV0 hQ hc1 a1
  have e2 := e1.correct hV1 (hQle _ (Nat.sub_le _ _)) hc2 a2
  have e3 := e2.correct hV2 (hQle _ (by omega)) hc3 a3
  have s0 := h0.sign hV0
  have s1 := e1.sign hV1
  have s2 := e2.sign hV2
  have s3 := e3.sign hV3
  -- Each sign is whether the estimate is still above the digit.
  have sg : ∀ x b, b = (if Rb < qOf D x then 1 else 0) → q ≤ x → b = if q < x then 1 else 0 := by
    intro x b hb hx
    by_cases c : q < x
    · rw [hb, ite_eq_left (mono x c), ite_eq_left c]
    · rw [hb, ite_eq_right (by have := mono' x (by omega); omega), ite_eq_right c]
  have g0 := sg _ _ s0 hlo
  have g1 := sg _ _ s1 (by rw [g0]; split <;> omega)
  have g2 := sg _ _ s2 (by rw [g1, g0]; split <;> split <;> omega)
  have g3 := sg _ _ s3 (by rw [g2, g1, g0]; split <;> split <;> split <;> omega)
  have hx : qh - b0 - b0 * (1 - c1) - b0 * (1 - c1) * (1 - c2) = q := by
    rw [g2, g1, g0]; split <;> split <;> split <;> omega
  refine ⟨hx, ?_, ?_⟩
  · rw [g3, hx, ite_eq_right (Nat.lt_irrefl _)]
  · have := e3.1
    rw [hx, show b0 * (1 - c1) * (1 - c2) * (1 - c3) = 0 by rw [g3, hx, ite_eq_right (Nat.lt_irrefl _)],
      Nat.zero_mul, Nat.add_zero] at this
    omega

/-! ## The first digit -/

theorem isqrt_lt_pow {x i : Nat} (h : x < 4 ^ i) : isqrt x < 2 ^ i := by
  refine Nat.lt_of_not_le fun c => ?_
  have := isqrt_sq_le x
  have : 2 ^ i * 2 ^ i ≤ isqrt x * isqrt x := Nat.mul_le_mul c c
  have h' : x < 2 ^ i * 2 ^ i := by rwa [← Nat.mul_pow]
  omega

theorem isqrt_zero : isqrt 0 = 0 := by
  have := isqrt_sq_le 0
  refine Nat.eq_zero_of_not_pos fun c => ?_
  have : 1 * 1 ≤ isqrt 0 * isqrt 0 := Nat.mul_le_mul c c
  omega

/-- The registers `pairStep`'s loop writes. -/
abbrev pairRegs : List Reg := [.a2, .a3, .a4, .a5, .a6, .a7, .s0, .s1, .t2, .t3, .t4, .t6, .t5]

theorem pairStep_ok (t : State) :
    WP isa (.block (pairStep ++ ([.addi .t5 .t5 (-1)] : List Instr))) t fun t' =>
      (t'.gpr .a2 = sh2 (t.gpr .a2) (t.gpr .a3) ∧ t'.gpr .a3 = t.gpr .a3 <<< 2 ∧
        t'.gpr .a4 = pR4 (t.gpr .a2) (t.gpr .a4) (t.gpr .a5) (t.gpr .s0) ∧
        t'.gpr .a5 = pR5 (t.gpr .a2) (t.gpr .a4) (t.gpr .a5) (t.gpr .s0) ∧
        t'.gpr .s0 = (t.gpr .s0 <<< 1 ||| (pB (t.gpr .a2) (t.gpr .a4) (t.gpr .a5) (t.gpr .s0) ^^^ 1#64)) ∧
        t'.mem = t.mem ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep pairRegs t t' := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold pairStep
  brun []

/-- `countLoop .t5 pairStep` from `T` in `a2:a3`, the root and remainder zero and `t5 = 64`: the root
`⌊√T⌋` in `s0` and the remainder `T - ⌊√T⌋²` in `a4:a5`. -/
theorem pairLoop_ok {s : State} (h0 : s.gpr .s0 = 0) (h4 : s.gpr .a4 = 0) (h5 : s.gpr .a5 = 0)
    (ht : s.gpr .t5 = BitVec.ofNat 64 64) :
    WP isa (countLoop .t5 pairStep) s fun t =>
      (t.gpr .s0).toNat = isqrt (v2 (s.gpr .a2) (s.gpr .a3)) ∧
        v2 (t.gpr .a4) (t.gpr .a5) + isqrt (v2 (s.gpr .a2) (s.gpr .a3)) * isqrt (v2 (s.gpr .a2) (s.gpr .a3)) =
          v2 (s.gpr .a2) (s.gpr .a3) ∧
        t.mem = s.mem ∧ Keep pairRegs s t := by
  have hT : v2 (s.gpr .a2) (s.gpr .a3) < 4 ^ 64 := by
    have := (s.gpr .a2).isLt; have := (s.gpr .a3).isLt; simp only [v2]; omega
  generalize hTe : v2 (s.gpr .a2) (s.gpr .a3) = T at hT ⊢
  let Inv : Nat → State → Prop := fun i t =>
    SqrtInv 64 T i (v2 (t.gpr .a2) (t.gpr .a3), v2 (t.gpr .a4) (t.gpr .a5), (t.gpr .s0).toNat) ∧
      t.mem = s.mem ∧ Keep pairRegs s t
  refine WP.mono (wp_countdown (body := .block (pairStep ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := 64) (by decide) (by decide) Inv (fun i hi t ⟨jI, jm, jk⟩ _ => ?_) ?_ ht) ?_
  · refine WP.mono (pairStep_ok t) fun t' ⟨⟨u2, u3, u4, u5, u0, um, u5'⟩, uk⟩ => ⟨⟨?_, by rw [um, jm],
      Keep.trans' jk uk⟩, u5'⟩
    -- The root is below `2^i ≤ 2^63`.
    have hy : (t.gpr .s0).toNat = isqrt (T / 4 ^ (64 - i)) := jI.2.1
    have hr : (t.gpr .s0).toNat < 2 ^ 63 := by
      rw [hy]
      refine Nat.lt_of_lt_of_le (isqrt_lt_pow (i := i) ?_) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add,
        show i + (64 - i) = 64 by omega]
      exact hT
    have e := pair_val (t.gpr .a2) (t.gpr .a3) (t.gpr .a4) (t.gpr .a5) (t.gpr .s0) hr
    have st := sqrtInv_step (nb := 128) (K := 64) hi (by
      have := isqrt_lt_pow (i := 64) hT; omega) jI
    rw [e] at st
    rw [u2, u3, u4, u5, u0]
    exact st
  · refine ⟨?_, rfl, Keep.refl _ _⟩
    have z : T / 4 ^ 64 = 0 := Nat.div_eq_of_lt hT
    refine ⟨?_, ?_, ?_⟩
    · show v2 (s.gpr .a2) (s.gpr .a3) = T % 4 ^ (64 - 0) * 4 ^ 0
      rw [hTe, Nat.sub_zero, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hT]
    · show (s.gpr .s0).toNat = isqrt (T / 4 ^ (64 - 0))
      rw [Nat.sub_zero, z, isqrt_zero, h0]; rfl
    · show v2 (s.gpr .a4) (s.gpr .a5) + (s.gpr .s0).toNat * (s.gpr .s0).toNat = T / 4 ^ (64 - 0)
      rw [Nat.sub_zero, z, h0, h4, h5]; rfl
  · intro t ⟨jI, jm, jk⟩
    obtain ⟨_, hy, hr⟩ := jI
    simp only [Nat.sub_self, Nat.pow_zero, Nat.div_one] at hy hr
    rw [← hy]
    exact ⟨rfl, by rw [hy] at hr ⊢; exact hr, jm, jk⟩

/-- `countLoop .t5 divBit` from `recipHead` (`a4 = 0`, `s3 = 2^64 - 1 - d`, `s4 = 0`, `t5 = 64`) for `d` in
`s2`: the memory and the registers but `recipRegs`' as they were, and where `d ≥ 2^63`, `s4 := v`. -/
theorem recLoop_ok {s : State} {d : Nat} (h2 : s.gpr .s2 = BitVec.ofNat 64 d) (hd : d < 2 ^ 64)
    (h4 : s.gpr .a4 = 0) (h3 : s.gpr .s3 = BitVec.ofNat 64 (2 ^ 64 - 1 - d)) (h4q : s.gpr .s4 = BitVec.ofNat 64 0)
    (ht : s.gpr .t5 = BitVec.ofNat 64 64) :
    WP isa (countLoop .t5 divBit) s fun t => t.mem = s.mem ∧ Keep [.s0, .s1, .s3, .s4, .t5] s t ∧
      (2 ^ 63 ≤ d → (t.gpr .s4).toNat = (2 ^ 128 - 1) / d - 2 ^ 64) := by
  by_cases hd63 : 2 ^ 63 ≤ d
  · have hr0 : 2 ^ 64 - 1 - d < d := by omega
    have h0 : RecInv s d (2 ^ 64 - 1 - d) 0 s :=
      ⟨Keep.refl _ _, rfl, 0, 2 ^ 64 - 1 - d, h3, h4q, by simp, hr0⟩
    refine WP.mono (wp_countdown (N := 64) (by decide) (by decide) (RecInv s d (2 ^ 64 - 1 - d))
      (fun k hk t hI _ => divStep_ok hd hr0 h4 h2 hk hI) h0 ht) fun t hI => ?_
    obtain ⟨q, r, _, h4t, hP, hr⟩ := hI.val
    refine ⟨hI.mem, hI.keep, fun _ => ?_⟩
    have hq : q = (2 ^ 128 - 1) / d - 2 ^ 64 := by
      rw [← VG.Proof.Bignum.WordStep.recip_eq hd (by omega), hP, Nat.mul_comm q, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr,
        Nat.add_zero]
    have hqB : q < 2 ^ 64 := by
      rw [hq]
      have : (2 ^ 128 - 1) / d < 2 ^ 65 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      omega
    rw [h4t, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqB, hq]
  · refine WP.mono (wp_countdown (N := 64) (by decide) (by decide)
      (fun _ t => t.mem = s.mem ∧ Keep [.s0, .s1, .s3, .s4, .t5] s t)
      (fun k hk t ⟨hm, hk'⟩ _ => WP.mono (divBit_ok t ((hk'.gpr (by decide)).trans h4))
        fun t' ⟨⟨_, _, um, u5⟩, uk⟩ => ⟨⟨by rw [um, hm], Keep.trans' hk' uk⟩, u5⟩) ⟨rfl, Keep.refl _ _⟩ ht)
      fun t ⟨hm, hk⟩ => ⟨hm, hk, fun c => absurd c hd63⟩

/-- The pointer of an array into `r`, the rest of a block after it. -/
theorem ptr1_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) {r : Reg}
    (h10 : r ≠ .s10) (h11 : r ≠ .s11) {a : Nat} (ha : a < 2048) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr r = off B (arr w a) → Keep [r] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r a ++ rest)) s Q :=
  ptr_ok h h10 h11 ha (k _ (by simp [gpr_write]) (Keep.write _ _ _) rfl)

/-- `fHead`: the top two words of `[wR]` (`W` words), `T`, into `a2:a3`, and the rest zero. -/
theorem fHead_ok {s : State} {B : Addr} {Z W N : Nat} (h : Ws s B Z W N) (hR : wR < N) (hW : 2 ≤ W) :
    WP isa (.block fHead) s fun t =>
      (t.gpr .s4 = off B (arr W wR) ∧ t.gpr .t1 = off B (arr W wR + 8 * W - 16) ∧
        t.gpr .a2 = word s.mem B (arr W wR + 8 * W - 16 + 8) ∧ t.gpr .a3 = word s.mem B (arr W wR + 8 * W - 16) ∧
        t.gpr .s0 = 0 ∧ t.gpr .a4 = 0 ∧ t.gpr .a5 = 0 ∧ t.gpr .t5 = BitVec.ofNat 64 64 ∧ t.mem = s.mem) ∧
      Keep [.s4, .t0, .t1, .a2, .a3, .s0, .a4, .a5, .t5] s t := by
  have fit := h.arr_fit hR
  have nw := h.nowrap
  have hS : S W = 8 * (W + 2) := rfl
  have al := arr_al W wR
  unfold fHead
  refine ptr1_ok h (by decide) (by decide) (by decide) fun u u4 uk um => ?_
  have hu := (h.of_keep uk).scr
  have u9 : u.gpr .s9 = BitVec.ofNat 64 W := (uk.gpr (by decide)).trans h.s9
  have e16 : off B (arr W wR + 8 * W) - BitVec.ofNat 64 16 = off B (arr W wR + 8 * W - 16) :=
    off_sub B (by omega_arith)
  refine WP.mono (WP.keep [.t0, .t1, .a2, .a3, .s0, .a4, .a5, .t5] (Q := fun t =>
      t.gpr .t1 = off B (arr W wR + 8 * W - 16) ∧
        t.gpr .a2 = word s.mem B (arr W wR + 8 * W - 16 + 8) ∧ t.gpr .a3 = word s.mem B (arr W wR + 8 * W - 16) ∧
        t.gpr .s0 = 0 ∧ t.gpr .a4 = 0 ∧ t.gpr .a5 = 0 ∧ t.gpr .t5 = BitVec.ofNat 64 64 ∧ t.mem = s.mem)
    ?_ (by rfl) (by rfl)) fun t ⟨q, k⟩ => ⟨⟨(k.gpr (by decide)).trans u4, q⟩, Keep.trans' (uk.mono (by decide)) (k.mono (by decide))⟩
  rw [← um]
  brun [u4, u9, shl3_ofNat, e16, fin64_exec_li_zero, exec_li_64,
    hu.ld (show arr W wR + 8 * W - 16 + 8 + 8 ≤ Z by omega_arith),
    hu.al8 (show arr W wR + 8 * W - 16 + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
    hu.ld (show arr W wR + 8 * W - 16 + 8 ≤ Z by omega_arith),
    hu.al8 (show arr W wR + 8 * W - 16 + 8 ≤ Z by omega_arith) (by omega_arith)]

/-- `fMid`: the remainder `a4:a5` over `T`, the root `s0` into `[wSN]`'s word `W / 2 - 1`, `s7 :=`
`[wSN]`'s address, and `recipHead` for `d = s0`. -/
theorem fMid_ok {s : State} {B : Addr} {Z W N : Nat} (h : Ws s B Z W N) (hR : wR < N) (hS : wSN < N)
    (hW : 2 ≤ W) (h1 : s.gpr .t1 = off B (arr W wR + 8 * W - 16)) :
    WP isa (.block fMid) s fun t =>
      (t.mem = ((s.mem.writeW (off B (arr W wR + 8 * W - 16)) (s.gpr .a5)).writeW
          (off B (arr W wR + 8 * W - 16 + 8)) (s.gpr .a4)).writeW (off B (arr W wSN + 8 * (W / 2) - 8)) (s.gpr .s0) ∧
        t.gpr .s7 = off B (arr W wSN) ∧ t.gpr .s2 = s.gpr .s0 ∧ t.gpr .a4 = 0 ∧
        t.gpr .s3 = BitVec.ofNat 64 (2 ^ 64 - 1 - (s.gpr .s0).toNat) ∧ t.gpr .s4 = BitVec.ofNat 64 0 ∧
        t.gpr .t5 = BitVec.ofNat 64 64 ∧ t.gpr .s0 = s.gpr .s0) ∧
      Keep [.s7, .t0, .s2, .a4, .s3, .s4, .t5] s t := by
  have fR := h.arr_fit hR
  have fS := h.arr_fit hS
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have alR := arr_al W wR
  have alS := arr_al W wSN
  have hs := h.scr
  have dRS := arr_disj (w := W) (show wR ≠ wSN by decide)
  unfold fMid
  simp only [List.append_assoc]
  rw [show ∀ l : List Instr, Instr.store .d .a5 .t1 0 :: Instr.store .d .a4 .t1 8 :: l =
    [Instr.store .d .a5 .t1 0, Instr.store .d .a4 .t1 8] ++ l from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = (s.mem.writeW (off B (arr W wR + 8 * W - 16)) (s.gpr .a5)).writeW
      (off B (arr W wR + 8 * W - 16 + 8)) (s.gpr .a4)) ?_ (by rfl) (by rfl)) fun u ⟨um, uk⟩ => ?_
  · brun [h1, hs.st (show arr W wR + 8 * W - 16 + 8 ≤ Z by omega_arith),
      hs.al8 (show arr W wR + 8 * W - 16 + 8 ≤ Z by omega_arith) (by omega_arith),
      hs.st (show arr W wR + 8 * W - 16 + 8 + 8 ≤ Z by omega_arith),
      hs.al8 (show arr W wR + 8 * W - 16 + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  have hu : Ws u B Z W N := ⟨h.scr.congr uk.2.2, h.fits, h.wpos, h.wle, (uk.gpr (by decide)).trans h.s9,
    (uk.gpr (by decide)).trans h.s10, (uk.gpr (by decide)).trans h.s11⟩
  refine ptr1_ok hu (by decide) (by decide) (by decide) fun v v7 vk vm => ?_
  have hv := (hu.of_keep vk).scr
  have v9 : v.gpr .s9 = BitVec.ofNat 64 W := (vk.gpr (by decide)).trans hu.s9
  have v0 : v.gpr .s0 = s.gpr .s0 := (vk.gpr (by decide)).trans (uk.gpr (by decide))
  have e8 : off B (arr W wSN + 8 * (W / 2)) - BitVec.ofNat 64 8 = off B (arr W wSN + 8 * (W / 2) - 8) :=
    off_sub B (by omega_arith)
  have hsub : BitVec.allOnes 64 - s.gpr .s0 = BitVec.ofNat 64 (2 ^ 64 - 1 - (s.gpr .s0).toNat) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .s0).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.t0, .s2, .a4, .s3, .s4, .t5] (Q := fun t =>
      t.mem = v.mem.writeW (off B (arr W wSN + 8 * (W / 2) - 8)) (s.gpr .s0) ∧ t.gpr .s2 = s.gpr .s0 ∧
        t.gpr .a4 = 0 ∧ t.gpr .s3 = BitVec.ofNat 64 (2 ^ 64 - 1 - (s.gpr .s0).toNat) ∧
        t.gpr .s4 = BitVec.ofNat 64 0 ∧ t.gpr .t5 = BitVec.ofNat 64 64)
    ?_ (by rfl) (by rfl)) fun t ⟨⟨tm, t2, t4, t3, t4q, t5⟩, tk⟩ => ⟨⟨by rw [tm, vm, um], by rw [tk.gpr (by decide), v7],
      t2, t4, t3, t4q, t5, by rw [tk.gpr (by decide), v0]⟩,
      Keep.trans' (Keep.trans' (uk.mono (by decide)) (vk.mono (by decide))) (tk.mono (by decide))⟩
  unfold recipHead
  brun [v7, v9, v0, mov, add_ofNat_zero', srl1_ofNat (show W < 2 ^ 64 by omega_arith), shl3_ofNat, e8, hsub,
    fin64_exec_li_zero, exec_li_m1, exec_li_64,
    hv.st (show arr W wSN + 8 * (W / 2) - 8 + 8 ≤ Z by omega_arith),
    hv.al8 (show arr W wSN + 8 * (W / 2) - 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  rfl

theorem seqs_one (c : Prog isa) : VG.Impl.Rsa.RISCV64.Keys.seqs [c] = c := rfl

/-- The registers `first` writes. -/
abbrev firstRegs : List Reg :=
  [.s4, .t0, .t1, .a2, .a3, .s0, .a4, .a5, .t5, .a6, .a7, .s1, .t2, .t3, .t4, .t6, .s7, .s2, .s3]

/-- `first`: of the top two words `T` of `[wR]` (`W` words), the root `y = ⌊√T⌋` into `[wSN]`'s word
`W / 2 - 1`, the remainder `T - y²` over `T`, and `y`'s reciprocal (where `y ≥ 2^63`) into `[wTmp]`'s
word 0; `s7 :=` `[wSN]`'s address. -/
theorem first_ok {s : State} {B : Addr} {Z W N : Nat} (h : Ws s B Z W N) (hR : wR < N) (hS : wSN < N)
    (hT : wTmp < N) (hW : 2 ≤ W) :
    WP isa first s fun t => Ws t B Z W N ∧ Keep firstRegs s t ∧ t.gpr .s7 = off B (arr W wSN) ∧
      ∃ r1 r0 y v : BitVec 64,
        t.mem = (((s.mem.writeW (off B (arr W wR + 8 * W - 16)) r0).writeW (off B (arr W wR + 8 * W - 16 + 8)) r1).writeW
          (off B (arr W wSN + 8 * (W / 2) - 8)) y).writeW (off B (arr W wTmp)) v ∧
        y.toNat = isqrt (v2 (word s.mem B (arr W wR + 8 * W - 16 + 8)) (word s.mem B (arr W wR + 8 * W - 16))) ∧
        v2 r1 r0 + y.toNat * y.toNat =
          v2 (word s.mem B (arr W wR + 8 * W - 16 + 8)) (word s.mem B (arr W wR + 8 * W - 16)) ∧
        (2 ^ 63 ≤ y.toNat → v.toNat = (2 ^ 128 - 1) / y.toNat - 2 ^ 64) := by
  have fT := h.arr_fit hT
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have alT := arr_al W wTmp
  unfold first
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (fHead_ok h hR hW) fun t1 ⟨⟨a4', u1, a2', a3', z0, z4, z5, t5', m1⟩, k1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (pairLoop_ok z0 z4 z5 t5') fun t2 ⟨y2, r2, m2, k2⟩ => ?_
  have k12 : Keep firstRegs s t2 := Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))
  have h2 : Ws t2 B Z W N := h.of_keep k12
  rw [a2', a3'] at y2 r2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  have t1' : t2.gpr .t1 = off B (arr W wR + 8 * W - 16) := (k2.gpr (by decide)).trans u1
  refine WP.mono (fMid_ok h2 hR hS hW t1') fun t3 ⟨⟨m3, s7', s2', a4'', s3', s4', t5'', s0'⟩, k3⟩ => ?_
  have h3 : Ws t3 B Z W N := h2.of_keep k3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (recLoop_ok (d := (t2.gpr .s0).toNat) (by rw [s2', BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (t2.gpr .s0).isLt a4'' s3' s4' t5'') fun t4 ⟨m4, k4, v4⟩ => ?_
  have h4 : Ws t4 B Z W N := h3.of_keep k4
  rw [seqs_one]
  refine ptr1_ok h4 (by decide) (by decide) (by decide) fun t5 t53 k5 m5 => ?_
  have hs5 := (h4.of_keep k5).scr
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t5.mem.writeW (off B (arr W wTmp)) (t5.gpr .s4))
    (by brun [t53, add_ofNat_zero', hs5.st (show arr W wTmp + 8 ≤ Z by omega_arith),
      hs5.al8 (show arr W wTmp + 8 ≤ Z by omega_arith) (by omega_arith)]) (by rfl) (by rfl))
    fun t ⟨tm, tk⟩ => ?_
  have kk : Keep firstRegs s t := Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans'
    (k1.mono (by decide)) (k2.mono (by decide))) (k3.mono (by decide))) (k4.mono (by decide)))
    (k5.mono (by decide))) (tk.mono (by decide))
  refine ⟨h.of_keep kk, kk, by rw [tk.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), s7'], ?_⟩
  have e4 : t5.gpr .s4 = t4.gpr .s4 := k5.gpr (by decide)
  refine ⟨t2.gpr .a4, t2.gpr .a5, t2.gpr .s0, t4.gpr .s4, by rw [tm, m5, m4, m3, m2, m1, e4], y2, by rw [y2]; exact r2,
    fun c => v4 c⟩

/-! ## A digit's estimate, by words -/

/-- The estimate a digit computes from `u = u₂:u₁`, `s₀`'s reciprocal `v` and `s₀`. -/
abbrev qhOf (v u2 u1 d : BitVec 64) : BitVec 64 := mgq v u2 u1 d ||| (0#64 - (bor u2 d ^^^ 1#64))

theorem qhOf_val {v u2 u1 d : BitVec 64} (hd : 2 ^ 63 ≤ d.toNat)
    (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (qhOf v u2 u1 d).toNat = min (2 ^ 64 - 1) (v2 u2 u1 / d.toNat) := by
  have hdl := d.isLt; have hu1 := u1.isLt; have hu2 := u2.isLt
  have hb := bor_toNat u2 d
  by_cases c : u2.toNat < d.toNat
  · have e : bor u2 d = 1#64 := BitVec.eq_of_toNat_eq (by rw [hb, ite_eq_left c]; rfl)
    have m := mgq_val (v := v.toNat) (u := u2.toNat) (a := u1.toNat) hdl hd c hu1 hv
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at m
    unfold qhOf
    rw [e, show (0#64 - (1#64 ^^^ 1#64)) = 0#64 from by decide, BitVec.or_zero, m]
    have : (u2.toNat * 2 ^ 64 + u1.toNat) / d.toNat < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have := Nat.mul_le_mul_right (2 ^ 64) (show u2.toNat + 1 ≤ d.toNat by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      rw [Nat.mul_comm]; omega
    simp only [v2]; omega
  · have e : bor u2 d = 0#64 := BitVec.eq_of_toNat_eq (by rw [hb, ite_eq_right c]; rfl)
    unfold qhOf
    rw [e, show (0#64 - (0#64 ^^^ 1#64)) = BitVec.allOnes 64 from by decide, BitVec.or_allOnes,
      BitVec.toNat_allOnes]
    have : 2 ^ 64 ≤ v2 u2 u1 / d.toNat := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := Nat.mul_le_mul_left (2 ^ 64) (show d.toNat ≤ u2.toNat by omega)
      simp only [v2]; rw [Nat.mul_comm u2.toNat]; omega
    omega

/-- A word and the next below, halved: `⌊(h 2^64 + l) / 2⌋ mod 2^64`. -/
abbrev half2 (h l : BitVec 64) : BitVec 64 := h <<< 63 ||| l >>> 1

theorem half2_toNat (h l : BitVec 64) : (half2 h l).toNat = (h.toNat % 2) * 2 ^ 63 + l.toNat / 2 := by
  have hl := l.isLt
  have h1 : (h <<< 63).toNat = (h.toNat % 2) * 2 ^ 63 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; have := h.isLt; omega
  have h2 : (l >>> 1).toNat = l.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd := sq_and_shl_small h (l >>> 1) 63 (by rw [h2]; omega)
  unfold half2
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hd, BitVec.toNat_add, h1, h2]
  omega

/-- The top three words `x₂ ≤ 1`, `x₁`, `x₀`, halved, as two words. -/
theorem u_val (x2 x1 x0 : BitVec 64) (h2 : x2.toNat ≤ 1) :
    v2 (half2 x2 x1) (half2 x1 x0) = (x2.toNat * 2 ^ 128 + x1.toNat * 2 ^ 64 + x0.toNat) / 2 := by
  have := x1.isLt; have := x0.isLt
  simp only [v2, half2_toNat]
  omega

theorem sq_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The registers `dLoad ++ dEst` writes. -/
abbrev dleRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a4, .a5, .a6, .a7, .s8]

/-- `dLoad ++ dEst`: `q̂` into `s8` from the remainder's top three words at `[wR]`'s words `W - m - 2` to
`W - m`, `s₀` (`s0`) and its reciprocal (`s1`). -/
theorem dLE_ok {s : State} {B : Addr} {Z W N m : Nat} (h : Ws s B Z W N) (hR : wR < N) (hm : m + 2 ≤ W)
    (h4 : s.gpr .s4 = off B (arr W wR)) (h2 : s.gpr .s2 = BitVec.ofNat 64 m) :
    WP isa (.block (dLoad ++ dEst)) s fun t =>
      (t.gpr .s8 = qhOf (s.gpr .s1) (half2 (word s.mem B (arr W wR + 8 * (W - m) - 16 + 16))
          (word s.mem B (arr W wR + 8 * (W - m) - 16 + 8)))
          (half2 (word s.mem B (arr W wR + 8 * (W - m) - 16 + 8)) (word s.mem B (arr W wR + 8 * (W - m) - 16)))
          (s.gpr .s0) ∧ t.mem = s.mem) ∧ Keep dleRegs s t := by
  have fit := h.arr_fit hR
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have al := arr_al W wR
  have hs := h.scr
  have e9 : BitVec.ofNat 64 W - BitVec.ofNat 64 m = BitVec.ofNat 64 (W - m) :=
    sq_sub_ofNat (by omega) (by have := h.wle; omega)
  have e16 : off B (arr W wR + 8 * (W - m)) - BitVec.ofNat 64 16 = off B (arr W wR + 8 * (W - m) - 16) :=
    off_sub B (by omega_arith)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [qhOf, mgq, half2, word, bor]
  unfold dLoad dEst
  brun [h.s9, h2, h4, e9, shl3_ofNat, e16, fin64_exec_li_zero,
    hs.ld (show arr W wR + 8 * (W - m) - 16 + 16 + 8 ≤ Z by omega_arith),
    hs.al8 (show arr W wR + 8 * (W - m) - 16 + 16 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.ld (show arr W wR + 8 * (W - m) - 16 + 8 + 8 ≤ Z by omega_arith),
    hs.al8 (show arr W wR + 8 * (W - m) - 16 + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
    hs.ld (show arr W wR + 8 * (W - m) - 16 + 8 ≤ Z by omega_arith),
    hs.al8 (show arr W wR + 8 * (W - m) - 16 + 8 ≤ Z by omega_arith) (by omega_arith)]
  rfl

theorem shl4_ofNat (a : Nat) : BitVec.ofNat 64 a <<< 4 = BitVec.ofNat 64 (16 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- `q̂²` off a word: the low word, and the carry `⌊q̂² / 2^64⌋` plus the borrow. -/
theorem sqw_arith (q x : BitVec 64) :
    (x - q * q).toNat + q.toNat * q.toNat =
      x.toNat + 2 ^ 64 * (BitVec.ofNat 64 (q.toNat * q.toNat / 2 ^ 64) + bor x (q * q)).toNat := by
  have k := msw_arith q q x 0#64
  have e : q * q + 0#64 = q * q := BitVec.add_zero _
  have b : bor (q * q) 0#64 = 0#64 := by
    unfold bor; rw [ite_eq_right (fun h => by simp [BitVec.lt_def] at h)]; rfl
  rw [e, b, BitVec.add_zero] at k
  simpa using k

/-- The registers `dPtr ++ dSq` writes. -/
abbrev dpsRegs : List Reg := [.a2, .t0, .a3, .t3, .t4, .t5, .t6, .a4, .a5, .a6, .t2, .a7]

/-- `dPtr ++ dSq`: `a2 :=` word `o = W - 2 m - 2` of `[wR]`, `a3 :=` word `k - m` of `[wSN]`, `q̂²` off
word `o`, the carry in `a4`, and `msBody`'s loop's pointers and count. -/
theorem dPS_ok {s : State} {B : Addr} {Z W N m k : Nat} (h : Ws s B Z W N) (hR : wR < N)
    (hk : W = 2 * k) (hm : m < k)
    (h4 : s.gpr .s4 = off B (arr W wR)) (h7 : s.gpr .s7 = off B (arr W wSN))
    (h2 : s.gpr .s2 = BitVec.ofNat 64 m) (h3 : s.gpr .s3 = BitVec.ofNat 64 k) :
    WP isa (.block (dPtr ++ dSq)) s fun t =>
      (t.gpr .a2 = off B (arr W wR + (8 * W - 16 * m - 16)) ∧ t.gpr .a3 = off B (arr W wSN + 8 * (k - m)) ∧
        t.gpr .a5 = off B (arr W wR + (8 * W - 16 * m - 16) + 8) ∧ t.gpr .a6 = off B (arr W wSN + 8 * (k - m)) ∧
        t.gpr .a7 = BitVec.ofNat 64 (m + 1) ∧ t.gpr .t2 = 0 ∧
        t.mem = s.mem.writeW (off B (arr W wR + (8 * W - 16 * m - 16)))
          (word s.mem B (arr W wR + (8 * W - 16 * m - 16)) - s.gpr .s8 * s.gpr .s8) ∧
        t.gpr .a4 = BitVec.ofNat 64 ((s.gpr .s8).toNat * (s.gpr .s8).toNat / 2 ^ 64) +
          bor (word s.mem B (arr W wR + (8 * W - 16 * m - 16))) (s.gpr .s8 * s.gpr .s8)) ∧
      Keep dpsRegs s t := by
  have fit := h.arr_fit hR
  have nw := h.nowrap
  have hle := h.wle
  have hSz : S W = 8 * (W + 2) := rfl
  have al := arr_al W wR
  have hs := h.scr
  have e1 : BitVec.ofNat 64 (8 * W) - BitVec.ofNat 64 (16 * m) = BitVec.ofNat 64 (8 * W - 16 * m) :=
    sq_sub_ofNat (by omega) (by omega)
  have e2 : BitVec.ofNat 64 (8 * W - 16 * m) - BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * W - 16 * m - 16) :=
    sq_sub_ofNat (by omega) (by omega)
  have e3 : BitVec.ofNat 64 k - BitVec.ofNat 64 m = BitVec.ofNat 64 (k - m) := sq_sub_ofNat (by omega) (by omega)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [word, bor]
  unfold dPtr dSq
  brun [h.s9, h2, h3, h4, h7, mov, add_ofNat_zero', shl4_ofNat, shl3_ofNat, e1, e2, e3, add_ofNat,
    fin64_exec_li_zero,
    hs.ld (show arr W wR + (8 * W - 16 * m - 16) + 8 ≤ Z by omega_arith),
    hs.st (show arr W wR + (8 * W - 16 * m - 16) + 8 ≤ Z by omega_arith),
    hs.al8 (show arr W wR + (8 * W - 16 * m - 16) + 8 ≤ Z by omega_arith) (by omega_arith)]

/-- A word less `c`: the borrow out. -/
theorem subw_arith (x c : BitVec 64) : (x - c).toNat + c.toNat = x.toNat + 2 ^ 64 * (bor x c).toNat := by
  have hx := x.isLt; have hc := c.isLt
  rw [BitVec.toNat_sub, bor_toNat]
  split <;> omega

/-- A word plus `c`: the carry out. -/
theorem addw_arith (x c : BitVec 64) : (x + c).toNat + 2 ^ 64 * (bor (x + c) c).toNat = x.toNat + c.toNat := by
  have hx := x.isLt; have hc := c.isLt
  rw [bor_toNat, BitVec.toNat_add]
  split <;> omega

/-- `dTop`: the word at `a5` less `a4`, the borrow into `a0`. -/
theorem dTop_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h5 : s.gpr .a5 = off B d)
    (hd : d + 8 ≤ Z) (hd8 : d % 8 = 0) :
    WP isa (.block dTop) s fun t =>
      (t.mem = s.mem.writeW (off B d) (word s.mem B d - s.gpr .a4) ∧ t.gpr .a0 = bor (word s.mem B d) (s.gpr .a4)) ∧
      Keep [.t5, .a0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [word, bor]
  unfold dTop
  brun [h5, add_ofNat_zero', hs.ld (show d + 8 ≤ Z from hd), hs.st (show d + 8 ≤ Z from hd), hs.al8 hd hd8]

/-- The registers `cHead` writes. -/
abbrev chRegs : List Reg := [.t2, .t3, .t4, .t5, .t6, .a4, .a5, .a6, .a7]

/-- `cHead`: under the mask `0 - a0`, `q̂ + (q̂ - 1)` added to word `o` (at `a2`), the carry into `a4`. -/
theorem cHead_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h2 : s.gpr .a2 = off B d)
    (hd : d + 8 ≤ Z) (hd8 : d % 8 = 0) :
    WP isa (.block cHead) s fun t =>
      (t.mem = s.mem.writeW (off B d) (word s.mem B d + (s.gpr .s8 &&& (0#64 - s.gpr .a0)) +
          ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0))) ∧
        t.gpr .a4 = bor (word s.mem B d + (s.gpr .s8 &&& (0#64 - s.gpr .a0))) (s.gpr .s8 &&& (0#64 - s.gpr .a0)) +
          bor (word s.mem B d + (s.gpr .s8 &&& (0#64 - s.gpr .a0)) + ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0)))
            ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0)) ∧
        t.gpr .t2 = 0#64 ∧ t.gpr .t3 = 0#64 - s.gpr .a0 ∧ t.gpr .a5 = off B (d + 8) ∧ t.gpr .a6 = s.gpr .a3 ∧
        t.gpr .a7 = s.gpr .s2 + BitVec.ofNat 64 1) ∧
      Keep chRegs s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [word, bor]
  unfold cHead
  brun [h2, mov, add_ofNat_zero', fin64_exec_li_zero, hs.ld (show d + 8 ≤ Z from hd),
    hs.st (show d + 8 ≤ Z from hd), hs.al8 hd hd8]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `cTail`: the carry `a4` into the word at `a5`, its carry out clearing `a0`, and `q̂ - a0`. -/
theorem cTail_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h5 : s.gpr .a5 = off B d)
    (hd : d + 8 ≤ Z) (hd8 : d % 8 = 0) :
    WP isa (.block cTail) s fun t =>
      (t.mem = s.mem.writeW (off B d) (word s.mem B d + s.gpr .a4) ∧ t.gpr .s8 = s.gpr .s8 - s.gpr .a0 ∧
        t.gpr .a0 = s.gpr .a0 &&& (bor (word s.mem B d + s.gpr .a4) (s.gpr .a4) ^^^ 1#64)) ∧
      Keep [.t6, .t4, .s8, .a0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  simp only [word, bor]
  unfold cTail
  brun [h5, add_ofNat_zero', hs.ld (show d + 8 ≤ Z from hd), hs.st (show d + 8 ≤ Z from hd), hs.al8 hd hd8]

/-- `dNext`: the digit `s8` into the word below `a3`, `m + 1` digits, one fewer to go. -/
theorem dNext_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h3 : s.gpr .a3 = off B d) (h8 : 8 ≤ d)
    (hd : d ≤ Z) (hd8 : d % 8 = 0) :
    WP isa (.block dNext) s fun t =>
      (t.mem = s.mem.writeW (off B (d - 8)) (s.gpr .s8) ∧ t.gpr .s2 = s.gpr .s2 + BitVec.ofNat 64 1 ∧
        t.gpr .a1 = s.gpr .a1 - BitVec.ofNat 64 1) ∧
      Keep [.t0, .s2, .a1] s t := by
  have e : off B d - BitVec.ofNat 64 8 = off B (d - 8) := off_sub B h8
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold dNext
  brun [h3, e, add_ofNat_zero', hs.st (show d - 8 + 8 ≤ Z by omega), hs.al8 (show d - 8 + 8 ≤ Z by omega) (by omega)]

/-- A window of words as its low word, `n` middle words and top word. -/
theorem wordsVal_split3 (mm : Mem) (B : Addr) (d n : Nat) :
    wordsVal mm B d (n + 2) = (word mm B d).toNat +
      2 ^ 64 * (wordsVal mm B (d + 8) n + 2 ^ (64 * n) * (word mm B (d + 8 + 8 * n)).toNat) := by
  rw [show n + 2 = (n + 1) + 1 from rfl, wordsVal, wordsVal_succ_top]

/-- The arithmetic of a window's three pieces. -/
theorem combine3 {P Q x0 x0' W1 W1' xt xt' c1 c2 c E S2 : Nat} (A : x0' + P * c1 = x0 + E)
    (Bq : W1' + Q * c2 = W1 + S2 + c1) (C : xt' + P * c = xt + c2) :
    x0' + P * (W1' + Q * xt') + P * Q * P * c = x0 + P * (W1 + Q * xt) + (E + P * S2) := by
  have h1 : (x0' + P * (W1' + Q * xt') + P * Q * P * c) + (P * c1 + P * Q * c2) =
      (x0' + P * c1) + P * (W1' + Q * c2) + P * Q * (xt' + P * c) := by ring
  have h2 : (x0 + P * (W1 + Q * xt) + (E + P * S2)) + (P * c1 + P * Q * c2) =
      (x0 + E) + P * (W1 + S2 + c1) + P * Q * (xt + c2) := by ring
  rw [A, Bq, C] at h1
  omega

/-- The registers `correct` writes. -/
abbrev corrRegs : List Reg := [.t2, .t3, .t4, .t5, .t6, .a4, .a5, .a6, .a7, .s8, .a0]

/-- `correct` on the window of `n + 2` words at `d` (`a2`), `S` the `n` words at `e` (`a3`), its top word
below `2^63`, the sign `b` in `a0` and `q̂` in `s8` (at least 1 where `b = 1`): `b (2 S β + 2 q̂ - 1)` added,
the carry out `c`, `q̂ - b` and the sign `b (1 - c)`. -/
theorem correct_ok {s : State} {B : Addr} {Z W N d e n : Nat} (h : Ws s B Z W N) (hR : wR < N) (hS : wSN < N)
    (hd : arr W wR ≤ d) (hdE : d + 8 * (n + 2) ≤ arr W wR + 8 * W) (he : arr W wSN ≤ e)
    (heE : e + 8 * n ≤ arr W wSN + 8 * W) (hd8 : d % 8 = 0) (he8 : e % 8 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 32)
    (h2 : s.gpr .a2 = off B d) (h3 : s.gpr .a3 = off B e) (h7 : s.gpr .s2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 n)
    (hb : (s.gpr .a0).toNat ≤ 1) :
    WP isa correct s fun t => Ws t B Z W N ∧ Keep corrRegs s t ∧ Outside B d (8 * (n + 2)) s.mem t.mem ∧
      (t.gpr .a0).toNat ≤ 1 ∧ t.gpr .a2 = s.gpr .a2 ∧ t.gpr .a3 = s.gpr .a3 ∧ t.gpr .s2 = s.gpr .s2 ∧
      (((s.gpr .a0).toNat = 1 → 1 ≤ (s.gpr .s8).toNat) → (word s.mem B (e + 8 * (n - 1))).toNat < 2 ^ 63 →
      ∃ c, c ≤ 1 ∧
        wordsVal t.mem B d (n + 2) + 2 ^ (64 * (n + 2)) * c =
          wordsVal s.mem B d (n + 2) +
            (s.gpr .a0).toNat * (2 * wordsVal s.mem B e n * 2 ^ 64 + 2 * (s.gpr .s8).toNat - 1) ∧
        (t.gpr .a0).toNat = (s.gpr .a0).toNat * (1 - c) ∧
        (t.gpr .s8).toNat = (s.gpr .s8).toNat - (s.gpr .a0).toNat) := by
  have fR := h.arr_fit hR
  have fS := h.arr_fit hS
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have dRS := arr_disj (w := W) (show wR ≠ wSN by decide)
  have hs := h.scr
  unfold correct
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (cHead_ok hs h2 (show d + 8 ≤ Z by omega_arith) hd8)
    fun t1 ⟨⟨m1, a41, t21, t31, a51, a61, a71⟩, k1⟩ => ?_
  have hs1 := hs.congr k1.2.2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (corLoop_ok (b := s.gpr .a0) hs1 a51 (a61.trans h3) (a71.trans h7) t21 t31 hb hn hn'
    (by omega) he8 (by omega_arith) (by omega_arith) (by omega_arith))
    fun t2 ⟨eq2, t22, out2, k2, a52, a62⟩ => ?_
  have hs2 := hs1.congr k2.2.2
  rw [seqs_one]
  have a52' : t2.gpr .a5 = off B (d + 8 + 8 * n) := a52
  refine WP.mono (cTail_ok hs2 a52' (show d + 8 + 8 * n + 8 ≤ Z by omega_arith) (by omega))
    fun t ⟨⟨m3, s83, a03⟩, k3⟩ => ?_
  have kk : Keep corrRegs s t :=
    Keep.trans' (Keep.trans' (k1.mono (by decide)) (k2.mono (by decide))) (k3.mono (by decide))
  -- The registers the pieces read, as they were.
  have q2 : t2.gpr .s8 = s.gpr .s8 := (k2.gpr (by decide)).trans (k1.gpr (by decide))
  have b2 : t2.gpr .a0 = s.gpr .a0 := (k2.gpr (by decide)).trans (k1.gpr (by decide))
  -- The words, through the writes.
  have w1 : t1.mem = s.mem.writeW (off B d) (word s.mem B d + (s.gpr .s8 &&& (0#64 - s.gpr .a0)) +
      ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0))) := m1
  have o1 : Outside B d 8 s.mem t1.mem := by rw [w1]; exact writeW_outside _ _ _ (by omega_arith)
  have S1 : wordsVal t1.mem B e n = wordsVal s.mem B e n := o1.wordsVal (by omega_arith) (by omega_arith)
  have W11 : wordsVal t1.mem B (d + 8) n = wordsVal s.mem B (d + 8) n := o1.wordsVal (by omega) (by omega_arith)
  have xt1 : word t1.mem B (d + 8 + 8 * n) = word s.mem B (d + 8 + 8 * n) := o1.word (by omega) (by omega_arith)
  have xt2 : word t2.mem B (d + 8 + 8 * n) = word s.mem B (d + 8 + 8 * n) := by
    rw [out2.word (by omega) (by omega_arith), xt1]
  have w3 : t.mem = t2.mem.writeW (off B (d + 8 + 8 * n)) (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) := m3
  have o3 : Outside B (d + 8 + 8 * n) 8 t2.mem t.mem := by rw [w3]; exact writeW_outside _ _ _ (by omega_arith)
  have hc : (bor (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) (t2.gpr .a4)).toNat ≤ 1 := by
    rw [bor_toNat]; split <;> omega
  refine ⟨h.of_keep kk, kk, ?_, ?_, kk.gpr (by decide), kk.gpr (by decide), kk.gpr (by decide), fun hq htop => ?_⟩
  · have o12 : Outside B d (8 * (n + 2)) s.mem t1.mem := o1.mono (by omega) (by omega)
    have o22 : Outside B d (8 * (n + 2)) t1.mem t2.mem := out2.mono (by omega) (by omega)
    have o32 : Outside B d (8 * (n + 2)) t2.mem t.mem := o3.mono (by omega) (by omega)
    exact (o12.trans o22).trans o32
  · rw [a03, b2]
    have := bor_toNat (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) (t2.gpr .a4)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
    · rw [show s.gpr .a0 = 0#64 from BitVec.eq_of_toNat_eq (by rw [h0]; rfl)]; simp
    · rw [show s.gpr .a0 = 1#64 from BitVec.eq_of_toNat_eq (by rw [h1]; rfl)]
      rw [BitVec.toNat_and]; exact Nat.le_trans Nat.and_le_left (by decide)
  have top0 : (t2.gpr .t2).toNat / 2 ^ 63 = 0 := by
    rw [t22, o1.word (by omega_arith) (by omega_arith)]; exact Nat.div_eq_of_lt htop
  have x0t : word t.mem B d = word s.mem B d + (s.gpr .s8 &&& (0#64 - s.gpr .a0)) +
      ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0)) := by
    rw [o3.word (by omega) (by omega_arith), out2.word (by omega) (by omega_arith), w1, word_writeW_self]
  have W1t : wordsVal t.mem B (d + 8) n = wordsVal t2.mem B (d + 8) n := o3.wordsVal (by omega) (by omega_arith)
  have xtt : word t.mem B (d + 8 + 8 * n) = word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4 := by
    rw [w3, word_writeW_self]
  -- The three pieces' sums.
  have A := corw_arith (word s.mem B d) (s.gpr .s8 &&& (0#64 - s.gpr .a0)) ((s.gpr .s8 - 1#64) &&& (0#64 - s.gpr .a0))
  rw [← a41, and_mask_toNat _ _ hb, and_mask_toNat _ _ hb] at A
  have Cq := addw_arith (word t2.mem B (d + 8 + 8 * n)) (t2.gpr .a4)
  rw [top0, Nat.mul_zero, Nat.add_zero, S1, W11] at eq2
  have hqb : (s.gpr .a0).toNat * (s.gpr .s8).toNat + (s.gpr .a0).toNat * (s.gpr .s8 - 1#64).toNat =
      (s.gpr .a0).toNat * (2 * (s.gpr .s8).toNat - 1) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
    · rw [h0]; simp
    · have q1 := hq h1
      have : (s.gpr .s8 - 1#64).toNat = (s.gpr .s8).toNat - 1 := by
        rw [BitVec.toNat_sub]; have := (s.gpr .s8).isLt; simp; omega
      rw [h1, this]; omega
  rw [Nat.add_assoc, hqb] at A
  refine ⟨(bor (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) (t2.gpr .a4)).toNat, hc, ?_, ?_, ?_⟩
  · rw [wordsVal_split3, wordsVal_split3, x0t, W1t, xtt]
    have e64 : 2 ^ (64 * (n + 2)) = 2 ^ 64 * 2 ^ (64 * n) * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    rw [e64]
    rw [← xt2]
    have := combine3 (P := 2 ^ 64) (Q := 2 ^ (64 * n)) A eq2 Cq
    rw [this]
    have hE : (s.gpr .a0).toNat * (2 * (s.gpr .s8).toNat - 1) + 2 ^ 64 * ((s.gpr .a0).toNat * (2 * wordsVal s.mem B e n)) =
        (s.gpr .a0).toNat * (2 * wordsVal s.mem B e n * 2 ^ 64 + 2 * (s.gpr .s8).toNat - 1) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
      · rw [h0]; simp
      · have := hq h1
        rw [h1, Nat.one_mul, Nat.one_mul, Nat.one_mul]
        have e : 2 ^ 64 * (2 * wordsVal s.mem B e n) = 2 * wordsVal s.mem B e n * 2 ^ 64 := by ring
        omega
    rw [hE]
  · rw [a03, b2]
    have hb2 := bor_toNat (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) (t2.gpr .a4)
    generalize bor (word t2.mem B (d + 8 + 8 * n) + t2.gpr .a4) (t2.gpr .a4) = cv at hb2 hc ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with c0 | c1
    all_goals first
      | (rw [show s.gpr .a0 = 0#64 from BitVec.eq_of_toNat_eq (by rw [h0]; rfl)]; simp)
      | (rw [show s.gpr .a0 = 1#64 from BitVec.eq_of_toNat_eq (by rw [h1]; rfl),
          show cv = 0#64 from BitVec.eq_of_toNat_eq (by rw [c0]; rfl)]; decide)
      | (rw [show s.gpr .a0 = 1#64 from BitVec.eq_of_toNat_eq (by rw [h1]; rfl),
          show cv = 1#64 from BitVec.eq_of_toNat_eq (by rw [c1]; rfl)]; decide)
  · rw [s83, q2, b2, BitVec.toNat_sub]
    have := (s.gpr .s8).isLt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
    · rw [h0]; omega
    · rw [h1]; have := hq h1; omega

/-- The arithmetic of a multiply-subtract's three pieces. -/
theorem msub3 {P Q q x0 x0' W1 W1' xt xt' c0 c1 b S2 : Nat} (A : x0' + q * q = x0 + P * c0)
    (Bq : W1' + q * S2 + c0 = W1 + Q * c1) (C : xt' + c1 = xt + P * b) :
    x0' + P * (W1' + Q * xt') + (q * q + P * (q * S2)) = x0 + P * (W1 + Q * xt) + P * Q * P * b := by
  have h1 : (x0' + P * (W1' + Q * xt') + (q * q + P * (q * S2))) + (P * c0 + P * Q * c1) =
      (x0' + q * q) + P * (W1' + q * S2 + c0) + P * Q * (xt' + c1) := by ring
  have h2 : (x0 + P * (W1 + Q * xt) + P * Q * P * b) + (P * c0 + P * Q * c1) =
      (x0 + P * c0) + P * (W1 + Q * c1) + P * Q * (xt + P * b) := by ring
  rw [A, Bq, C] at h1
  omega

/-- A number below `2^(64 m)` of `m + 1` words: its top word is zero. -/
theorem top_zero {mm : Mem} {B : Addr} {e m : Nat} (h : wordsVal mm B e (m + 1) < 2 ^ (64 * m)) :
    word mm B (e + 8 * m) = 0 := by
  rw [wordsVal_succ_top] at h
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ (64 * m) * (word mm B (e + 8 * m)).toNat < 2 ^ (64 * m) * 1 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  show (word mm B (e + 8 * m)).toNat = 0
  omega

/-- A number at most `2^(64 m + 1)` of `m + 1` words: its top word is at most 1. -/
theorem top_le_one {mm : Mem} {B : Addr} {e m : Nat} (h : wordsVal mm B e (m + 1) < 2 * 2 ^ (64 * m)) :
    (word mm B (e + 8 * m)).toNat ≤ 1 := by
  rw [wordsVal_succ_top] at h
  have : 2 ^ (64 * m) * (word mm B (e + 8 * m)).toNat < 2 ^ (64 * m) * 2 := by omega
  have := Nat.lt_of_mul_lt_mul_left this
  omega

/-- The top three words of a window of `m + 3`, the top one at most 1, halved: `⌊V / (2 β^m)⌋`. -/
theorem win_u (mm : Mem) (B : Addr) (d m : Nat) (h2 : (word mm B (d + 8 * (m + 2))).toNat ≤ 1) :
    v2 (half2 (word mm B (d + 8 * (m + 2))) (word mm B (d + 8 * (m + 1))))
      (half2 (word mm B (d + 8 * (m + 1))) (word mm B (d + 8 * m))) =
      wordsVal mm B d (m + 3) / (2 * 2 ^ (64 * m)) := by
  rw [u_val _ _ _ h2, wordsVal_append mm B d m 3]
  have e3 : wordsVal mm B (d + 8 * m) 3 = (word mm B (d + 8 * m)).toNat +
      2 ^ 64 * ((word mm B (d + 8 * (m + 1))).toNat + 2 ^ 64 * (word mm B (d + 8 * (m + 2))).toNat) := by
    simp only [wordsVal]
    rw [show d + 8 * m + 8 = d + 8 * (m + 1) by omega, show d + 8 * (m + 1) + 8 = d + 8 * (m + 2) by omega]
    simp
  rw [e3, Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]
  congr 1
  ring

/-- What a digit takes off is below `β^(m+3)`. -/
theorem qOf_lt {Sv qh m : Nat} (hS : Sv < 2 ^ (64 * m)) (hq : qh ≤ 2 ^ 64 - 1) :
    qOf (2 * Sv * 2 ^ 64) qh < 2 ^ (64 * (m + 3)) := by
  have e : 2 ^ (64 * (m + 3)) = 2 ^ (64 * m) * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, show 64 * (m + 3) = 64 * m + 64 + 64 + 64 by omega]
  rw [e]
  generalize hA : 2 ^ (64 * m) = A at *
  have hA1 : 1 ≤ A := by rw [← hA]; exact Nat.one_le_two_pow
  generalize hb : (2 : Nat) ^ 64 = β at *
  have hβ : 4 ≤ β := by rw [← hb]; decide
  -- `q̂ (2 S β + q̂) ≤ (β - 1) (2 (A - 1) β + β) < β · 2 A β ≤ A β β β`.
  have h1 : qh * (2 * Sv * β + qh) ≤ (β - 1) * (2 * Sv * β + (β - 1)) := Nat.mul_le_mul hq (by omega)
  have h2 : 2 * Sv * β + (β - 1) < 2 * A * β := by
    have : (Sv + 1) * β ≤ A * β := Nat.mul_le_mul_right _ hS
    have e1 : 2 * A * β = 2 * (A * β) := by ring
    have e2 : 2 * Sv * β = 2 * (Sv * β) := by ring
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have h3 : (β - 1) * (2 * Sv * β + (β - 1)) < β * (2 * A * β) :=
    Nat.mul_lt_mul_of_le_of_lt (by omega) h2 (by omega)
  have h4 : β * (2 * A * β) ≤ A * β * β * β := by
    have e : β * (2 * A * β) = A * β * β * 2 := by ring
    rw [e]; exact Nat.mul_le_mul_left _ (by omega)
  unfold qOf
  omega

/-- The registers `digit` writes. -/
abbrev digRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a2, .a3, .a4, .a5, .a6, .a7, .s8, .s2, .a1]

/-- A digit, `m` so far (`1 ≤ m < k`, `W = 2 k`): on the window of `m + 3` words of `[wR]` at word
`W - 2 m - 2`, the remainder `R` (its `m + 1` words from word 2) and the next pair `P` (its words 0 and 1),
and the root `S`, the `m + 1` words of `[wSN]` from word `k - m`: the remainder less `q (2 S β + q)` for the
digit `q`, and `q` into `[wSN]`'s word `k - m - 1`, where `s₀ = ⌊S / β^(m-1)⌋ ≥ 2^63`, `s1` its reciprocal and
`R ≤ 2 S`. -/
theorem digit_ok {s : State} {B : Addr} {Z W N m k : Nat} (h : Ws s B Z W N) (hR : wR < N) (hS : wSN < N)
    (hk : W = 2 * k) (hm1 : 1 ≤ m) (hmk : m < k)
    (h4 : s.gpr .s4 = off B (arr W wR)) (h7 : s.gpr .s7 = off B (arr W wSN))
    (h2 : s.gpr .s2 = BitVec.ofNat 64 m) (h3 : s.gpr .s3 = BitVec.ofNat 64 k) :
    WP isa digit s fun t => Ws t B Z W N ∧ Keep digRegs s t ∧ t.gpr .s2 = BitVec.ofNat 64 (m + 1) ∧
      t.gpr .a1 = s.gpr .a1 - BitVec.ofNat 64 1 ∧
      ∃ (mid : Mem) (y : BitVec 64), Outside B (arr W wR + (8 * W - 16 * m - 16)) (8 * (m + 3)) s.mem mid ∧
        t.mem = mid.writeW (off B (arr W wSN + 8 * (k - m) - 8)) y ∧
        ∀ Sv R P q, wordsVal s.mem B (arr W wSN + 8 * (k - m)) (m + 1) = Sv →
          wordsVal s.mem B (arr W wR + (8 * W - 16 * m - 16) + 16) (m + 1) = R →
          wordsVal s.mem B (arr W wR + (8 * W - 16 * m - 16)) 2 = P →
          Sv / 2 ^ (64 * (m - 1)) = (s.gpr .s0).toNat → 2 ^ 63 ≤ (s.gpr .s0).toNat → R ≤ 2 * Sv →
          IsDigit (2 ^ 64) Sv (R * (2 ^ 64 * 2 ^ 64) + P) q →
          (s.gpr .s1).toNat = (2 ^ 128 - 1) / (s.gpr .s0).toNat - 2 ^ 64 →
          wordsVal mid B (arr W wR + (8 * W - 16 * m - 16)) (m + 3) =
            R * (2 ^ 64 * 2 ^ 64) + P - qOf (2 * Sv * 2 ^ 64) q ∧ y.toNat = q := by
  have fR := h.arr_fit hR
  have fS := h.arr_fit hS
  have nw := h.nowrap
  have hle := h.wle
  have hSz : S W = 8 * (W + 2) := rfl
  have alR := arr_al W wR
  have alS := arr_al W wSN
  have dRS := arr_disj (w := W) (show wR ≠ wSN by decide)
  generalize hd : arr W wR + (8 * W - 16 * m - 16) = d
  generalize he : arr W wSN + 8 * (k - m) = e
  have hd16 : d + 16 + 8 * m = arr W wR + 8 * (W - m) - 16 + 16 := by omega
  have hd8m : d + 8 * m = arr W wR + 8 * (W - m) - 16 := by omega
  have hd8m1 : d + 8 * (m + 1) = arr W wR + 8 * (W - m) - 16 + 8 := by omega
  have c1 : arr W wR ≤ d := by omega
  have c2 : d + 8 * (m + 1 + 2) ≤ arr W wR + 8 * W := by omega
  have c3 : arr W wSN ≤ e := by omega
  have c4 : e + 8 * (m + 1) ≤ arr W wSN + 8 * W := by omega
  have c5 : d % 8 = 0 := by omega
  have c6 : e % 8 = 0 := by omega
  have c7 : 1 ≤ m + 1 := by omega
  have c8 : m + 1 < 2 ^ 32 := by omega
  unfold digit
  rw [wp_seqs_cons (List.cons_ne_nil _ _),
    show dLoad ++ dEst ++ dPtr ++ dSq = (dLoad ++ dEst) ++ (dPtr ++ dSq) from List.append_assoc _ _ _,
    WP.block_append_iff]
  refine WP.mono (dLE_ok h hR (by omega) h4 h2) fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have hu : Ws u B Z W N := h.of_keep uk
  refine WP.mono (dPS_ok hu hR hk hmk ((uk.gpr (by decide)).trans h4) ((uk.gpr (by decide)).trans h7)
    ((uk.gpr (by decide)).trans h2) ((uk.gpr (by decide)).trans h3))
    fun t1 ⟨⟨a21, a31, a51, a61, a71, t21, m1, a41⟩, k1⟩ => ?_
  rw [hd] at a21 a51 m1 a41
  rw [he] at a31 a61
  have h1 : Ws t1 B Z W N := hu.of_keep k1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (msLoop_ok (n := m + 1) h1.scr a51 a61 a71 t21 (by omega) (by omega) (by omega) (by omega)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun t2 ⟨eq2, t22, out2, k2, a52, a62⟩ => ?_
  have h2' : Ws t2 B Z W N := h1.of_keep k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dTop_ok (d := d + 8 + 8 * (m + 1)) h2'.scr a52 (by omega_arith) (by omega))
    fun t3 ⟨⟨m3, a03⟩, k3⟩ => ?_
  have h3' : Ws t3 B Z W N := h2'.of_keep k3
  -- Registers through the multiply-subtract.
  have kA : Keep digRegs s t3 := Keep.trans' (Keep.trans' (Keep.trans' (uk.mono (by decide)) (k1.mono (by decide)))
    (k2.mono (by decide))) (k3.mono (by decide))
  have a23 : t3.gpr .a2 = off B d := (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans a21)
  have a33 : t3.gpr .a3 = off B e := (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans a31)
  have s23' : t3.gpr .s2 + BitVec.ofNat 64 1 = BitVec.ofNat 64 (m + 1) := by
    rw [(k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans ((k1.gpr (by decide)).trans ((uk.gpr (by decide)).trans h2))),
      add_ofNat]
  have hb3 : (t3.gpr .a0).toNat ≤ 1 := by rw [a03, bor_toNat]; split <;> omega
  -- The three corrections.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (correct_ok (n := m + 1) (d := d) (e := e) h3' hR hS c1 c2 c3 c4 c5 c6 c7 c8 a23 a33 s23' hb3) fun t4 ⟨h4', k4, o4, b4, a24, a34, s24, v4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (correct_ok (n := m + 1) (d := d) (e := e) h4' hR hS c1 c2 c3 c4 c5 c6 c7 c8 (a24.trans a23) (a34.trans a33) (by rw [s24]; exact s23') b4)
    fun t5 ⟨h5', k5, o5, b5, a25, a35, s25, v5⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (correct_ok (n := m + 1) (d := d) (e := e) h5' hR hS c1 c2 c3 c4 c5 c6 c7 c8 ((a25.trans a24).trans a23) ((a35.trans a34).trans a33)
    (by rw [s25, s24]; exact s23') b5)
    fun t6 ⟨h6', k6, o6, b6, a26, a36, s26, v6⟩ => ?_
  rw [seqs_one]
  have a36' : t6.gpr .a3 = off B e := ((a36.trans a35).trans a34).trans a33
  refine WP.mono (dNext_ok h6'.scr a36' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨⟨m7, s27, a17⟩, k7⟩ => ?_
  have kk : Keep digRegs s t := Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' kA (k4.mono (by decide)))
    (k5.mono (by decide))) (k6.mono (by decide))) (k7.mono (by decide))
  refine ⟨h6'.of_keep k7, kk, ?_, ?_, t6.mem, t6.gpr .s8, ?_, by rw [m7, ← he], ?_⟩
  · rw [s27, s26, s25, s24, s23']
  · rw [a17, k6.gpr (by decide), k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide),
      k1.gpr (by decide), uk.gpr (by decide)]
  · -- The memory, but the window.
    have oU : Outside B d (8 * (m + 3)) s.mem u.mem := by rw [um]; exact Outside.refl _ _ _ _
    have o1 : Outside B d (8 * (m + 3)) u.mem t1.mem :=
      (by rw [m1]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega) (by omega))
    have o2 : Outside B d (8 * (m + 3)) t1.mem t2.mem := out2.mono (by omega) (by omega)
    have o3 : Outside B d (8 * (m + 3)) t2.mem t3.mem :=
      (by rw [m3]; exact (writeW_outside _ _ _ (by omega_arith)).mono (by omega) (by omega))
    exact ((((((oU.trans o1).trans o2).trans o3).trans o4).trans o5).trans o6)
  · intro Sv R P q hSv hRv hPv hd0 hd1 hR2 hq hv
    rw [← hd] at hRv hPv ⊢
    rw [← he] at hSv
    rw [hd] at hRv hPv ⊢
    rw [he] at hSv
    -- The window, `R β² + P`.
    have V0 : wordsVal s.mem B d (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P := by
      have := wordsVal_append s.mem B d 2 (m + 1)
      rw [show 2 + (m + 1) = m + 3 by omega, show d + 8 * 2 = d + 16 by omega, hRv, hPv] at this
      rw [this, show 2 ^ (64 * 2) = 2 ^ 64 * 2 ^ 64 by rfl]; ring
    have hPl : P < 2 ^ 64 * 2 ^ 64 := by rw [← hPv]; exact wordsVal_lt _ _ _ _
    -- `S < β^m`, its top word zero; `R`'s top word at most 1.
    have d0l := (s.gpr .s0).isLt
    have hSl : Sv < 2 ^ (64 * m) := by
      have e : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hd0]; exact d0l
    have sTop : word s.mem B (e + 8 * m) = 0 := top_zero (by rw [hSv]; exact hSl)
    have rTop : (word s.mem B (d + 16 + 8 * m)).toNat ≤ 1 := top_le_one (by rw [hRv]; omega)
    -- The estimate.
    have u1q : t1.gpr .s8 = u.gpr .s8 := k1.gpr (by decide)
    have q3 : t3.gpr .s8 = u.gpr .s8 := (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans u1q)
    have hwin := win_u s.mem B d m (by rw [show d + 8 * (m + 2) = d + 16 + 8 * m by omega]; exact rTop)
    rw [show d + 8 * (m + 2) = arr W wR + 8 * (W - m) - 16 + 16 by omega,
      show d + 8 * (m + 1) = arr W wR + 8 * (W - m) - 16 + 8 by omega,
      show d + 8 * m = arr W wR + 8 * (W - m) - 16 by omega, V0] at hwin
    have qv := qhOf_val (v := s.gpr .s1) (u2 := half2 (word s.mem B (arr W wR + 8 * (W - m) - 16 + 16))
      (word s.mem B (arr W wR + 8 * (W - m) - 16 + 8)))
      (u1 := half2 (word s.mem B (arr W wR + 8 * (W - m) - 16 + 8)) (word s.mem B (arr W wR + 8 * (W - m) - 16)))
      (d := s.gpr .s0) hd1 hv
    rw [← u8] at qv
    rw [hwin] at qv
    obtain ⟨qlo, qhi⟩ := est_bounds hm1 hd0 hd1 hR2 hPl hq
    rw [← qv] at qlo qhi
    -- The multiply-subtract, `Enc` with the sign `b₀`.
    have w1 : t1.mem = s.mem.writeW (off B d) (word s.mem B d - u.gpr .s8 * u.gpr .s8) := by
      rw [m1, um, ← u1q]
    have o1 : Outside B d 8 s.mem t1.mem := by rw [w1]; exact writeW_outside _ _ _ (by omega_arith)
    have Se1 : wordsVal t1.mem B e (m + 1) = Sv := by rw [o1.wordsVal (by omega_arith) (by omega_arith), hSv]
    have W11 : wordsVal t1.mem B (d + 8) (m + 1) = wordsVal s.mem B (d + 8) (m + 1) :=
      o1.wordsVal (by omega) (by omega_arith)
    have tb0 : (t2.gpr .t2).toNat / 2 ^ 63 = 0 := by
      rw [t22, show m + 1 - 1 = m by omega, o1.word (by omega_arith) (by omega_arith), sTop]; rfl
    rw [tb0, Nat.mul_zero, Nat.add_zero, Se1, W11, u1q] at eq2
    have xt2 : word t2.mem B (d + 8 + 8 * (m + 1)) = word s.mem B (d + 8 + 8 * (m + 1)) := by
      rw [out2.word (by omega) (by omega_arith), o1.word (by omega) (by omega_arith)]
    have w3 : t3.mem = t2.mem.writeW (off B (d + 8 + 8 * (m + 1)))
        (word t2.mem B (d + 8 + 8 * (m + 1)) - t2.gpr .a4) := m3
    have o3 : Outside B (d + 8 + 8 * (m + 1)) 8 t2.mem t3.mem := by
      rw [w3]; exact writeW_outside _ _ _ (by omega_arith)
    have A := sqw_arith (u.gpr .s8) (word s.mem B d)
    have c0 : t1.gpr .a4 = BitVec.ofNat 64 ((u.gpr .s8).toNat * (u.gpr .s8).toNat / 2 ^ 64) +
        bor (word s.mem B d) (u.gpr .s8 * u.gpr .s8) := by rw [a41, um]
    rw [← c0] at A
    have C := subw_arith (word t2.mem B (d + 8 + 8 * (m + 1))) (t2.gpr .a4)
    rw [← a03] at C
    have x03 : word t3.mem B d = word s.mem B d - u.gpr .s8 * u.gpr .s8 := by
      rw [o3.word (by omega) (by omega_arith), out2.word (by omega) (by omega_arith), w1, word_writeW_self]
    have W13 : wordsVal t3.mem B (d + 8) (m + 1) = wordsVal t2.mem B (d + 8) (m + 1) :=
      o3.wordsVal (by omega) (by omega_arith)
    have xt3 : word t3.mem B (d + 8 + 8 * (m + 1)) = word t2.mem B (d + 8 + 8 * (m + 1)) - t2.gpr .a4 := by
      rw [w3, word_writeW_self]
    have e64 : 2 ^ (64 * (m + 1 + 2)) = 2 ^ 64 * 2 ^ (64 * (m + 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
    have key : ∀ x, qOf (2 * Sv * 2 ^ 64) x = x * x + 2 ^ 64 * (x * (2 * Sv)) := fun x => by unfold qOf; ring
    have E0 : Enc (2 ^ (64 * (m + 1 + 2))) (2 * Sv * 2 ^ 64) (R * (2 ^ 64 * 2 ^ 64) + P) (wordsVal t3.mem B d (m + 1 + 2)) (u.gpr .s8).toNat (t3.gpr .a0).toNat := by
      refine ⟨?_, hb3⟩
      rw [wordsVal_split3, x03, W13, xt3, key, ← V0, show m + 3 = m + 1 + 2 from rfl, wordsVal_split3, ← xt2,
        e64]
      rw [msub3 (P := 2 ^ 64) (Q := 2 ^ (64 * (m + 1))) A eq2 C]
      ring
    have hEpos : ∀ x, wordsVal x B d (m + 1 + 2) < 2 ^ (64 * (m + 1 + 2)) := fun x => wordsVal_lt _ _ _ _
    have hQ0 : qOf (2 * Sv * 2 ^ 64) (u.gpr .s8).toNat < 2 ^ (64 * (m + 1 + 2)) :=
      qOf_lt hSl (by rw [qv]; exact Nat.min_le_left _ _)
    -- `b = 1` only where `q̂ ≥ 1`.
    have pos : ∀ {V qh b : Nat}, Enc (2 ^ (64 * (m + 1 + 2))) (2 * Sv * 2 ^ 64) (R * (2 ^ 64 * 2 ^ 64) + P) V qh b →
        V < 2 ^ (64 * (m + 1 + 2)) → b = 1 → 1 ≤ qh := fun {V qh b} h hV hb => by
      have sg := h.sign hV
      rw [hb] at sg
      rcases Nat.eq_zero_or_pos qh with h0 | h0
      · rw [h0] at sg; simp only [qOf, Nat.zero_mul] at sg; split at sg <;> omega
      · exact h0
    -- `S` and its top word, through the writes in the window.
    have oS : ∀ {mm : Mem}, Outside B d (8 * (m + 3)) s.mem mm →
        wordsVal mm B e (m + 1) = Sv ∧ word mm B (e + 8 * (m + 1 - 1)) = 0 := fun {mm} o => by
      refine ⟨by rw [o.wordsVal (by omega_arith) (by omega_arith), hSv], ?_⟩
      rw [show m + 1 - 1 = m by omega, o.word (by omega_arith) (by omega_arith), sTop]
    have o3' : Outside B d (8 * (m + 3)) s.mem t3.mem := by
      have oa : Outside B d (8 * (m + 3)) s.mem t1.mem := o1.mono (by omega) (by omega)
      have ob : Outside B d (8 * (m + 3)) t1.mem t2.mem := out2.mono (by omega) (by omega)
      have oc : Outside B d (8 * (m + 3)) t2.mem t3.mem := o3.mono (by omega) (by omega)
      exact (oa.trans ob).trans oc
    have o4' := o3'.trans o4
    have o5' := o4'.trans o5
    obtain ⟨S3, T3⟩ := oS o3'
    obtain ⟨S4, T4⟩ := oS o4'
    obtain ⟨S5, T5⟩ := oS o5'
    have z : (0#64).toNat < 2 ^ 63 := by decide
    have q3' : (t3.gpr .s8).toNat = (u.gpr .s8).toNat := by rw [q3]
    obtain ⟨c1, hc1, a1, b1, q1⟩ := v4 (by rw [q3']; exact pos E0 (hEpos _)) (by rw [T3]; exact z)
    rw [S3, q3'] at a1
    rw [q3'] at q1
    have E1 := E0.correct (hEpos _) hQ0 hc1 a1
    rw [← b1, ← q1] at E1
    obtain ⟨c2, r2⟩ := v5 (pos E1 (hEpos _)) (by rw [T4]; exact z)
    have hc2 := r2.1
    have a2 := r2.2.1
    have b2 := r2.2.2.1
    have q2 := r2.2.2.2
    rw [S4] at a2
    have hQ1 : qOf (2 * Sv * 2 ^ 64) (t4.gpr .s8).toNat < 2 ^ (64 * (m + 1 + 2)) :=
      Nat.lt_of_le_of_lt (qOf_mono (show (t4.gpr .s8).toNat ≤ (u.gpr .s8).toNat by rw [q1]; exact Nat.sub_le _ _))
        hQ0
    have E2 := E1.correct (hEpos _) hQ1 hc2 a2
    rw [← b2, ← q2] at E2
    obtain ⟨c3, r3⟩ := v6 (pos E2 (hEpos _)) (by rw [T5]; exact z)
    have hc3 := r3.1
    have a3 := r3.2.1
    have q3e := r3.2.2.2
    rw [S5] at a3
    rw [q1, b1] at a2
    rw [q2, b2, q1, b1] at a3
    rw [q2, b2, q1, b1] at q3e
    have dig1 : qOf (2 * Sv * 2 ^ 64) q ≤ R * (2 ^ 64 * 2 ^ 64) + P := by
      unfold qOf; rw [Nat.mul_comm]; exact hq.1
    have dig2 : R * (2 ^ 64 * 2 ^ 64) + P < qOf (2 * Sv * 2 ^ 64) (q + 1) := by
      unfold qOf; rw [Nat.mul_comm (q + 1)]; exact hq.2
    obtain ⟨hx, _, hV3⟩ := Enc.three dig1 dig2 qlo qhi E0 (hEpos _) (hEpos _) (hEpos _) (hEpos _) hQ0 hc1 hc2 hc3
      a1 a2 a3
    exact ⟨by rw [show m + 3 = m + 1 + 2 from rfl]; exact hV3, by rw [q3e, hx]⟩

/-! ## The digits -/

/-- A number `S 2^(64 j)` of `j + n` words: its low `j` words are zero and the rest are `S`. -/
theorem wv_low_zero {mm : Mem} {B : Addr} {p j n S : Nat} (h : wordsVal mm B p (j + n) = S * 2 ^ (64 * j)) :
    wordsVal mm B p j = 0 ∧ wordsVal mm B (p + 8 * j) n = S := by
  rw [wordsVal_append] at h
  have hl := wordsVal_lt mm B p j
  generalize wordsVal mm B p j = L at *
  generalize wordsVal mm B (p + 8 * j) n = H at *
  generalize 2 ^ (64 * j) = A at *
  have hA : 0 < A := by omega
  have e1 : (L + A * H) % A = L := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  have e2 : (S * A) % A = 0 := Nat.mul_mod_left _ _
  rw [h] at e1
  have hL : L = 0 := by omega
  subst hL
  refine ⟨rfl, ?_⟩
  rw [Nat.zero_add] at h
  exact Nat.eq_of_mul_eq_mul_left hA (by rw [h, Nat.mul_comm])

/-- A number below `2^(64 a)` of `a + b` words: its low `a` words are it and the rest zero. -/
theorem wv_prefix {mm : Mem} {B : Addr} {p a b R : Nat} (h : wordsVal mm B p (a + b) = R) (hR : R < 2 ^ (64 * a)) :
    wordsVal mm B p a = R ∧ wordsVal mm B (p + 8 * a) b = 0 := by
  rw [wordsVal_append] at h
  have hl := wordsVal_lt mm B p a
  generalize wordsVal mm B p a = L at *
  generalize wordsVal mm B (p + 8 * a) b = H at *
  generalize 2 ^ (64 * a) = A at *
  rcases Nat.eq_zero_or_pos H with h0 | h0
  · subst h0; omega
  · have : A * 1 ≤ A * H := Nat.mul_le_mul_left _ h0; omega

/-- A word written where it was zero adds it at its place. -/
theorem wv_write_zero {mm : Mem} {B : Addr} {p i n : Nat} (y : BitVec 64) (h0 : word mm B (p + 8 * i) = 0)
    (hi : i < n) (fit : p + 8 * n ≤ 2 ^ 64) :
    wordsVal (mm.writeW (off B (p + 8 * i)) y) B p n = wordsVal mm B p n + 2 ^ (64 * i) * y.toNat := by
  obtain ⟨r, rfl⟩ : ∃ r, n = i + 1 + r := ⟨n - i - 1, by omega⟩
  have o := writeW_outside mm B (d := p + 8 * i) y (by omega)
  rw [wordsVal_append _ _ _ (i + 1) r, wordsVal_append _ _ _ (i + 1) r, wordsVal_succ_top, wordsVal_succ_top, h0,
    word_writeW_self, o.wordsVal (by omega) (by omega), o.wordsVal (by omega) (by omega)]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
  ring

/-- After `m` digits (`W = 2 k`): the root `S` at `[wSN]`'s word `k - m` up (`d₀` its top word), the low
`W - 2 m` words of `[wR]` those of `Xn`, the remainder `R ≤ 2 S` in the `2 m` words above, and
`S² + R = ⌊Xn / β^(W - 2 m)⌋`. -/
def DV (mm : Mem) (B : Addr) (W k m Xn d0 : Nat) : Prop :=
  ∃ Sv R, wordsVal mm B (arr W wSN) W = Sv * 2 ^ (64 * (k - m)) ∧ Sv / 2 ^ (64 * (m - 1)) = d0 ∧
    wordsVal mm B (arr W wR) (W - 2 * m) = Xn % 2 ^ (64 * (W - 2 * m)) ∧
    wordsVal mm B (arr W wR + 8 * (W - 2 * m)) (2 * m) = R ∧ R ≤ 2 * Sv ∧
    Sv * Sv + R = Xn / 2 ^ (64 * (W - 2 * m))

/-- A digit's step of `DV`: the window of `m + 3` words at word `W - 2 m - 2` of `[wR]` the new remainder,
and the digit at `[wSN]`'s word `k - m - 1`. -/
theorem dv_step {m0 mid : Mem} {B : Addr} {W k m Xn d0 : Nat} {y : BitVec 64}
    (hk : W = 2 * k) (hm1 : 1 ≤ m) (hmk : m < k) (hd0 : d0 < 2 ^ 64)
    (fitR : arr W wR + S W ≤ 2 ^ 64) (fitS : arr W wSN + S W ≤ 2 ^ 64)
    (h : DV m0 B W k m Xn d0)
    (hout : Outside B (arr W wR + (8 * W - 16 * m - 16)) (8 * (m + 3)) m0 mid)
    (hval : ∀ Sv R P q, wordsVal m0 B (arr W wSN + 8 * (k - m)) (m + 1) = Sv →
      wordsVal m0 B (arr W wR + (8 * W - 16 * m - 16) + 16) (m + 1) = R →
      wordsVal m0 B (arr W wR + (8 * W - 16 * m - 16)) 2 = P → Sv / 2 ^ (64 * (m - 1)) = d0 → R ≤ 2 * Sv →
      IsDigit (2 ^ 64) Sv (R * (2 ^ 64 * 2 ^ 64) + P) q →
      wordsVal mid B (arr W wR + (8 * W - 16 * m - 16)) (m + 3) = R * (2 ^ 64 * 2 ^ 64) + P - qOf (2 * Sv * 2 ^ 64) q ∧
        y.toNat = q) :
    DV (mid.writeW (off B (arr W wSN + 8 * (k - m) - 8)) y) B W k (m + 1) Xn d0 := by
  obtain ⟨Sv, R, hS, hd, hlow, hRv, hR2, hSR⟩ := h
  have hSz : S W = 8 * (W + 2) := rfl
  have dRS := arr_disj (w := W) (show wR ≠ wSN by decide)
  unfold DV
  generalize hpR : arr W wR = pR at *
  generalize hpS : arr W wSN = pS at *
  generalize ho : W - 2 * m = o at *
  have ho2 : 2 ≤ o := by omega
  have hdo : pR + (8 * W - 16 * m - 16) = pR + 8 * (o - 2) := by omega
  rw [hdo] at hout hval
  rw [show pR + 8 * (o - 2) + 16 = pR + 8 * o by omega] at hval
  -- `S < β^m`.
  have hSl : Sv < 2 ^ (64 * m) := by
    have e : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by
      rw [← Nat.pow_add, show 64 * m = 64 + 64 * (m - 1) by omega]
    rw [e, ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hd]; exact hd0
  have hβm : 2 ^ (64 * m) * 2 ^ 64 = 2 ^ (64 * (m + 1)) := by
    rw [← Nat.pow_add, show 64 * m + 64 = 64 * (m + 1) by omega]
  -- The root's words.
  obtain ⟨low0, hhigh⟩ := wv_low_zero (j := k - m) (n := W - (k - m))
    (by rw [show k - m + (W - (k - m)) = W by omega]; exact hS)
  obtain ⟨Sv1, _⟩ := wv_prefix (a := m + 1) (b := W - (k - m) - (m + 1))
    (by rw [show m + 1 + (W - (k - m) - (m + 1)) = W - (k - m) by omega]; exact hhigh)
    (Nat.lt_of_lt_of_le hSl (Nat.pow_le_pow_right (n := 2) (by decide) (show 64 * m ≤ 64 * (m + 1) by omega)))
  -- The remainder's words.
  have hRl : R < 2 ^ (64 * (m + 1)) := by
    rw [← hβm]
    have : 2 ^ (64 * m) * 2 ≤ 2 ^ (64 * m) * 2 ^ 64 := Nat.mul_le_mul_left _ (by decide)
    omega
  obtain ⟨Rv1, Rhi0⟩ := wv_prefix (a := m + 1) (b := m - 1)
    (by rw [show m + 1 + (m - 1) = 2 * m by omega]; exact hRv) hRl
  -- The next pair and the low words.
  have hlow2 := hlow
  rw [show o = (o - 2) + 2 by omega, wordsVal_append] at hlow2
  have hPl := wordsVal_lt m0 B (pR + 8 * (o - 2)) 2
  have hLl := wordsVal_lt m0 B pR (o - 2)
  have eo : 2 ^ (64 * (o - 2 + 2)) = 2 ^ (64 * (o - 2)) * (2 ^ 64 * 2 ^ 64) := by
    rw [← Nat.pow_add, ← Nat.pow_add, show 64 * (o - 2 + 2) = 64 * (o - 2) + (64 + 64) by omega]
  rw [eo] at hlow2
  generalize hP : wordsVal m0 B (pR + 8 * (o - 2)) 2 = P at *
  generalize hL : wordsVal m0 B pR (o - 2) = L at *
  have hP' : P = Xn / 2 ^ (64 * (o - 2)) % (2 ^ 64 * 2 ^ 64) := by
    rw [← Nat.mod_mul_right_div_self, ← hlow2, Nat.mul_comm (2 ^ (64 * (o - 2))) P,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hLl, Nat.zero_add]
  have hL' : L = Xn % 2 ^ (64 * (o - 2)) := by
    rw [← Nat.mod_mul_right_mod Xn (2 ^ (64 * (o - 2))) (2 ^ 64 * 2 ^ 64), ← hlow2,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLl]
  have hA : Xn / 2 ^ (64 * (o - 2)) = Xn / 2 ^ (64 * o) * (2 ^ 64 * 2 ^ 64) + P := by
    rw [hP']
    have h1 := Nat.div_add_mod (Xn / 2 ^ (64 * (o - 2))) (2 ^ 64 * 2 ^ 64)
    have h2 : Xn / 2 ^ (64 * (o - 2)) / (2 ^ 64 * 2 ^ 64) = Xn / 2 ^ (64 * o) := by
      rw [Nat.div_div_eq_div_mul, ← eo, show o - 2 + 2 = o by omega]
    rw [h2] at h1
    rw [Nat.mul_comm (Xn / 2 ^ (64 * o))]
    exact h1.symm
  -- The digit.
  have hq := digit_isqrt (β := 2 ^ 64) (P := P) hSR
  generalize hqd : isqrt (Xn / 2 ^ (64 * o) * (2 ^ 64 * 2 ^ 64) + P) - Sv * 2 ^ 64 = q at hq
  obtain ⟨hwin, hy⟩ := hval Sv R P q Sv1 Rv1 rfl hd hR2 hq
  obtain ⟨st1, st2⟩ := VG.Proof.Bignum.SqrtRem.step_inv (β := 2 ^ 64) (P := P) hSR hq
  have hqβ : q < 2 ^ 64 := digit_lt hR2 (show P < 2 ^ 64 * 2 ^ 64 from hPl) hq.1
  have qe : qOf (2 * Sv * 2 ^ 64) q = (2 * Sv * 2 ^ 64 + q) * q := Nat.mul_comm _ _
  rw [qe] at hwin
  -- The writes, outside the regions.
  have ow := writeW_outside mid B (d := pS + 8 * (k - m) - 8) y (by omega)
  refine ⟨Sv * 2 ^ 64 + q, R * (2 ^ 64 * 2 ^ 64) + P - (2 * Sv * 2 ^ 64 + q) * q, ?_, ?_, ?_, ?_, st2, ?_⟩
  · -- The root, with the digit below.
    have w0 : word mid B (pS + 8 * (k - m - 1)) = 0 := by
      rw [hout.word (by omega) (by omega)]
      have := wordsVal_zero_part low0 (a := k - m - 1) (c := 1) (by omega)
      apply BitVec.eq_of_toNat_eq
      simpa [wordsVal] using this
    have hS' : wordsVal mid B pS W = Sv * 2 ^ (64 * (k - m)) := by
      rw [hout.wordsVal (by omega) (by omega), hS]
    rw [show pS + 8 * (k - m) - 8 = pS + 8 * (k - m - 1) by omega, wv_write_zero y w0 (by omega) (by omega), hS', hy,
      show k - (m + 1) = k - m - 1 by omega]
    have e : 2 ^ (64 * (k - m)) = 2 ^ (64 * (k - m - 1)) * 2 ^ 64 := by
      rw [← Nat.pow_add, show 64 * (k - m) = 64 * (k - m - 1) + 64 by omega]
    rw [e]; ring
  · -- The top word.
    rw [show m + 1 - 1 = m by omega]
    have e : 2 ^ (64 * m) = 2 ^ 64 * 2 ^ (64 * (m - 1)) := by
      rw [← Nat.pow_add, show 64 * m = 64 + 64 * (m - 1) by omega]
    rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm Sv, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hqβ,
      Nat.add_zero, hd]
  · -- The low words.
    rw [show W - 2 * (m + 1) = o - 2 by omega]
    rw [ow.wordsVal (by omega) (by omega), hout.wordsVal (by omega) (by omega), hL, hL']
  · -- The remainder: the window, then the words above it, zero.
    rw [show W - 2 * (m + 1) = o - 2 by omega, show 2 * (m + 1) = (m + 3) + (m - 1) by omega, wordsVal_append,
      ow.wordsVal (by omega) (by omega), ow.wordsVal (by omega) (by omega), hwin,
      hout.wordsVal (by omega) (by omega), show pR + 8 * (o - 2) + 8 * (m + 3) = pR + 8 * o + 8 * (m + 1) by omega,
      Rhi0, Nat.mul_zero, Nat.add_zero]
  · rw [show W - 2 * (m + 1) = o - 2 by omega, hA]
    exact st1

/-- `dsHead`: `s4 :=` `[wR]`'s address, `s1 := v` (`[wTmp]`'s word 0), `s3 := k`, `s0 := s₀` (`[wSN]`'s word
`k - 1`), one digit so far and `k - 1` to go. -/
theorem dsHead_ok {s : State} {B : Addr} {Z W N k : Nat} (h : Ws s B Z W N) (hS : wSN < N)
    (hT : wTmp < N) (hk : W = 2 * k) (hk1 : 1 ≤ k) (h7 : s.gpr .s7 = off B (arr W wSN)) :
    WP isa (.block dsHead) s fun t =>
      (t.gpr .s4 = off B (arr W wR) ∧ t.gpr .s1 = word s.mem B (arr W wTmp) ∧ t.gpr .s3 = BitVec.ofNat 64 k ∧
        t.gpr .s0 = word s.mem B (arr W wSN + 8 * k - 8) ∧ t.gpr .s2 = BitVec.ofNat 64 1 ∧
        t.gpr .a1 = BitVec.ofNat 64 (k - 1) ∧ t.mem = s.mem) ∧
      Keep [.t3, .s4, .s1, .s3, .t0, .s0, .s2, .a1] s t := by
  have fS := h.arr_fit hS
  have fT := h.arr_fit hT
  have nw := h.nowrap
  have hle := h.wle
  have hSz : S W = 8 * (W + 2) := rfl
  have alS := arr_al W wSN
  have alT := arr_al W wTmp
  unfold dsHead
  refine ptr2_ok h (r := .t3) (r' := .s4) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u u3 u4 uk um => ?_
  have hu := (h.of_keep uk).scr
  have u9 : u.gpr .s9 = BitVec.ofNat 64 W := (uk.gpr (by decide)).trans h.s9
  have u7 : u.gpr .s7 = off B (arr W wSN) := (uk.gpr (by decide)).trans h7
  have e8 : off B (arr W wSN + 8 * k) - BitVec.ofNat 64 8 = off B (arr W wSN + 8 * k - 8) := off_sub B (by omega)
  have ek : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) := sq_sub_ofNat hk1 (by omega)
  have hk2 : W / 2 = k := by omega
  refine WP.mono (WP.keep [.s1, .s3, .t0, .s0, .s2, .a1] (Q := fun t =>
      t.gpr .s1 = word s.mem B (arr W wTmp) ∧ t.gpr .s3 = BitVec.ofNat 64 k ∧
        t.gpr .s0 = word s.mem B (arr W wSN + 8 * k - 8) ∧ t.gpr .s2 = BitVec.ofNat 64 1 ∧
        t.gpr .a1 = BitVec.ofNat 64 (k - 1) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun t ⟨⟨t1, t3, t0, t2, ta, tm⟩, tk⟩ => ⟨⟨by rw [tk.gpr (by decide), u4], t1, t3, t0, t2, ta, tm⟩,
      Keep.trans' (uk.mono (by decide)) (tk.mono (by decide))⟩
  rw [← um]
  simp only [word]
  brun [u3, u7, u9, srl1_ofNat (show W < 2 ^ 64 by omega), hk2, shl3_ofNat, e8, ek, r2_exec_li_one,
    add_ofNat_zero', hu.ld (show arr W wTmp + 8 ≤ Z by omega_arith),
    hu.al8 (show arr W wTmp + 8 ≤ Z by omega_arith) (by omega_arith),
    hu.ld (show arr W wSN + 8 * k - 8 + 8 ≤ Z by omega_arith),
    hu.al8 (show arr W wSN + 8 * k - 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  rfl

/-- The registers `digits` writes. -/
abbrev dsRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a2, .a3, .a4, .a5, .a6, .a7, .s8, .s2, .a1, .s4, .s1, .s3, .s0]

/-- `digits`: the `k - 1` digits after the first (`W = 2 k`), from `DV` after one digit to `DV` after `k`,
for `s₀` (`[wSN]`'s word `k - 1`) at least `2^63` and `v` (`[wTmp]`'s word 0) its reciprocal; only `[wR]` and
`[wSN]` change. -/
theorem digits_ok {s : State} {B : Addr} {Z W N k : Nat} (h : Ws s B Z W N) (hR : wR < N) (hS : wSN < N)
    (hT : wTmp < N) (hk : W = 2 * k) (hk2 : 2 ≤ k) (h7 : s.gpr .s7 = off B (arr W wSN)) :
    WP isa digits s fun t => Ws t B Z W N ∧ Keep dsRegs s t ∧ Frame B W [wR, wSN] [] s.mem t.mem ∧
      ∀ Xn, 2 ^ 63 ≤ (word s.mem B (arr W wSN + 8 * k - 8)).toNat →
        (word s.mem B (arr W wTmp)).toNat = (2 ^ 128 - 1) / (word s.mem B (arr W wSN + 8 * k - 8)).toNat - 2 ^ 64 →
        DV s.mem B W k 1 Xn (word s.mem B (arr W wSN + 8 * k - 8)).toNat →
        DV t.mem B W k k Xn (word s.mem B (arr W wSN + 8 * k - 8)).toNat := by
  have fR := h.arr_fit hR
  have fS := h.arr_fit hS
  have nw := h.nowrap
  have hle := h.wle
  have hSz : S W = 8 * (W + 2) := rfl
  unfold digits
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (dsHead_ok h hS hT hk (by omega) h7) fun u ⟨⟨u4, u1, u3, u0, u2, ua, um⟩, uk⟩ => ?_
  rw [seqs_one]
  have hu : Ws u B Z W N := h.of_keep uk
  have u7 : u.gpr .s7 = off B (arr W wSN) := (uk.gpr (by decide)).trans h7
  let Inv : Nat → State → Prop := fun i t => Ws t B Z W N ∧ t.gpr .s4 = off B (arr W wR) ∧
    t.gpr .s7 = off B (arr W wSN) ∧ t.gpr .s3 = BitVec.ofNat 64 k ∧ t.gpr .s2 = BitVec.ofNat 64 (i + 1) ∧
    t.gpr .s0 = u.gpr .s0 ∧ t.gpr .s1 = u.gpr .s1 ∧ Keep digRegs u t ∧ Frame B W [wR, wSN] [] u.mem t.mem ∧
    ∀ Xn, 2 ^ 63 ≤ (u.gpr .s0).toNat → (u.gpr .s1).toNat = (2 ^ 128 - 1) / (u.gpr .s0).toNat - 2 ^ 64 →
      DV u.mem B W k 1 Xn (u.gpr .s0).toNat → DV t.mem B W k (i + 1) Xn (u.gpr .s0).toNat
  refine WP.mono (wp_countdown (body := digit) (cnt := .a1) (N := k - 1) (by omega) (by omega) Inv
    (fun i hi t ⟨jw, j4, j7, j3, j2, j0, j1, jk, jf, jv⟩ _ => ?_)
    ⟨hu, u4, u7, u3, u2, rfl, rfl, Keep.refl _ _, Frame.refl _ _ _ _ _, fun _ _ _ h => h⟩ ua)
    fun t ⟨tw, _, _, _, _, _, _, tk, tf, tv⟩ => ⟨tw, Keep.trans' (uk.mono (by decide)) (tk.mono (by decide)),
      by rw [← um]; exact tf, fun Xn hd hv h1 => ?_⟩
  · refine WP.mono (digit_ok (m := i + 1) jw hR hS hk (by omega) (by omega) j4 j7 j2 j3)
      fun t' ⟨w', k', s2', a1', mid, y, hout, hm, hval⟩ => ⟨⟨w', ?_, ?_, ?_, s2', ?_, ?_, Keep.trans' jk (k'.mono (by decide)),
        ?_, ?_⟩, a1'⟩
    · exact (k'.gpr (by decide)).trans j4
    · exact (k'.gpr (by decide)).trans j7
    · exact (k'.gpr (by decide)).trans j3
    · exact (k'.gpr (by decide)).trans j0
    · exact (k'.gpr (by decide)).trans j1
    · -- Only `[wR]`'s window and `[wSN]`'s word change.
      have f1 : Frame B W [wR, wSN] [] t.mem mid :=
        Frame.of_arr (o := wR) (d := 8 * W - 16 * (i + 1) - 16) hout (by omega) (by simp)
      have f2 : Frame B W [wR, wSN] [] mid t'.mem := by
        rw [hm, show arr W wSN + 8 * (k - (i + 1)) - 8 = arr W wSN + (8 * (k - (i + 1)) - 8) by omega]
        exact Frame.of_arr (o := wSN) (writeW_outside _ _ _ (by omega_arith)) (by omega) (by simp)
      exact (jf.trans f1).trans f2
    · intro Xn hd1 hv h1
      rw [hm]
      refine dv_step (m := i + 1) hk (by omega) (by omega) (u.gpr .s0).isLt (h.fit64 hR) (h.fit64 hS)
        (jv Xn hd1 hv h1) hout fun Sv R P q a b c dd e f => hval Sv R P q a b c (by rw [j0]; exact dd)
          (by rw [j0]; exact hd1) e f (by rw [j1, j0]; exact hv)
  · have := tv Xn (by rw [u0]; exact hd) (by rw [u1, u0]; exact hv) (by rw [um, u0]; exact h1)
    rw [show k - 1 + 1 = k by omega, u0] at this
    exact this

/-! ## Normalization -/

/-- The word at the top nonzero index `hi` of a number below `2^(64 (hi + 1))`: its quotient by `2^(64 hi)`. -/
theorem top_word_div {mm : Mem} {B : Addr} {p W hi : Nat} (hhi : hi < W)
    (hX : wordsVal mm B p W < 2 ^ (64 * (hi + 1))) :
    (word mm B (p + 8 * hi)).toNat = wordsVal mm B p W / 2 ^ (64 * hi) := by
  have e := wordsVal_append mm B p hi (W - hi)
  rw [show hi + (W - hi) = W by omega] at e
  obtain ⟨r, hr⟩ : ∃ r, W - hi = r + 1 := ⟨W - hi - 1, by omega⟩
  rw [hr, wordsVal] at e
  have hl := wordsVal_lt mm B p hi
  have hw := (word mm B (p + 8 * hi)).isLt
  -- The words above `hi` are zero.
  have hz : wordsVal mm B (p + 8 * hi + 8) r = 0 := by
    rcases Nat.eq_zero_or_pos (wordsVal mm B (p + 8 * hi + 8) r) with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ (64 * hi) * (2 ^ 64 * 1) ≤
          2 ^ (64 * hi) * ((word mm B (p + 8 * hi)).toNat + 2 ^ 64 * wordsVal mm B (p + 8 * hi + 8) r) :=
        Nat.mul_le_mul_left _ (by have := Nat.mul_le_mul_left (2 ^ 64) h0; omega)
      have e2 : 2 ^ (64 * (hi + 1)) = 2 ^ (64 * hi) * (2 ^ 64 * 1) := by
        rw [Nat.mul_one, ← Nat.pow_add, show 64 * hi + 64 = 64 * (hi + 1) by omega]
      omega
  rw [hz, Nat.mul_zero, Nat.add_zero] at e
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hl, Nat.zero_add]

/-- Normalized by the even part of its leading zeros, a number has its top two bits not both zero:
`X 2^c₂ ∈ [2^(64 W - 2), 2^(64 W))`, for `clz = 64 (W - 1 - hi) + z`, `T = ⌊X / 2^(64 hi)⌋` and
`2^63 ≤ T 2^z < 2^64`. -/
theorem norm_bounds {X T hi z W : Nat} (hT : T = X / 2 ^ (64 * hi))
    (hhi : hi < W) (hz : z ≤ 63) (h1 : 2 ^ 63 ≤ T * 2 ^ z) (h2 : T * 2 ^ z < 2 ^ 64) :
    2 ^ (64 * W - 2) ≤ X * 2 ^ ((64 * (W - 1 - hi) + z) / 2 * 2) ∧
      X * 2 ^ ((64 * (W - 1 - hi) + z) / 2 * 2) < 2 ^ (64 * W) := by
  generalize hc : 64 * (W - 1 - hi) + z = clz
  have hc2 : clz / 2 * 2 ≤ clz ∧ clz ≤ clz / 2 * 2 + 1 := by omega
  -- `X 2^clz = (T 2^z) 2^(64 (W - 1)) + (X mod 2^(64 hi)) 2^clz`.
  have hX' := Nat.div_add_mod X (2 ^ (64 * hi))
  rw [← hT] at hX'
  have hl := Nat.mod_lt X (Nat.two_pow_pos (64 * hi))
  generalize X % 2 ^ (64 * hi) = L at hX' hl
  have eA : 2 ^ (64 * hi) * 2 ^ clz = 2 ^ z * 2 ^ (64 * (W - 1)) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← hc]; congr 1; omega
  -- `(T + 1) 2^z ≤ 2^64`: `T 2^z` is a multiple of `2^z` below `2^64`.
  have hT1 : (T + 1) * 2 ^ z ≤ 2 ^ 64 := by
    have e : 2 ^ 64 = 2 ^ (64 - z) * 2 ^ z := by rw [← Nat.pow_add]; congr 1; omega
    rw [e] at h2 ⊢
    exact Nat.mul_le_mul_right _ (Nat.lt_of_mul_lt_mul_right h2)
  have lo : 2 ^ (64 * W - 1) ≤ X * 2 ^ clz := by
    have e : 2 ^ (64 * W - 1) = 2 ^ 63 * 2 ^ (64 * (W - 1)) := by rw [← Nat.pow_add]; congr 1; omega
    calc 2 ^ (64 * W - 1) = 2 ^ 63 * 2 ^ (64 * (W - 1)) := e
      _ ≤ T * 2 ^ z * 2 ^ (64 * (W - 1)) := Nat.mul_le_mul_right _ h1
      _ = 2 ^ (64 * hi) * T * 2 ^ clz := by
          rw [Nat.mul_comm (2 ^ (64 * hi)) T, Nat.mul_assoc T (2 ^ (64 * hi)), eA, Nat.mul_assoc]
      _ ≤ X * 2 ^ clz := Nat.mul_le_mul_right _ (by omega)
  have hi' : X * 2 ^ clz < 2 ^ (64 * W) := by
    have e : 2 ^ (64 * W) = 2 ^ 64 * 2 ^ (64 * (W - 1)) := by rw [← Nat.pow_add]; congr 1; omega
    calc X * 2 ^ clz < 2 ^ (64 * hi) * (T + 1) * 2 ^ clz :=
          Nat.mul_lt_mul_of_pos_right (by rw [Nat.mul_add, Nat.mul_one]; omega) (Nat.two_pow_pos _)
      _ = (T + 1) * 2 ^ z * 2 ^ (64 * (W - 1)) := by
          rw [Nat.mul_comm (2 ^ (64 * hi)), Nat.mul_assoc, eA, Nat.mul_assoc]
      _ ≤ 2 ^ 64 * 2 ^ (64 * (W - 1)) := Nat.mul_le_mul_right _ hT1
      _ = 2 ^ (64 * W) := e.symm
  refine ⟨?_, Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hc2.1)) hi'⟩
  -- `X 2^c₂ ≥ X 2^clz / 2`.
  rcases Nat.lt_or_ge (clz / 2 * 2) clz with c | c
  · have e : clz = clz / 2 * 2 + 1 := by omega
    rw [e, Nat.pow_succ, ← Nat.mul_assoc] at lo
    have e2 : 2 ^ (64 * W - 1) = 2 ^ (64 * W - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    rw [e2] at lo
    exact Nat.le_of_mul_le_mul_right lo (by decide)
  · rw [show clz / 2 * 2 = clz by omega]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) lo

/-- The last nonzero of `f`'s first `i` values (0 where there is none). -/
def topOf (f : Nat → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | i + 1 => if f i = 0 then topOf f i else f i

/-- Of at least one value, the last nonzero is the value at `hiIdx`. -/
theorem topOf_hi (f : Nat → BitVec 64) : ∀ {k}, 1 ≤ k → topOf f k = f (hiIdx f k)
  | 0, h => absurd h (by decide)
  | 1, _ => by
    simp only [topOf, hiIdx]
    by_cases hz : f 0 = 0
    · rw [ite_eq_left hz, ite_eq_left hz, hz]
    · rw [ite_eq_right hz, ite_eq_right hz]
  | k + 2, _ => by
    simp only [topOf, hiIdx]
    by_cases hz : f (k + 1) = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact topOf_hi f (k := k + 1) (by omega)
    · rw [ite_eq_right hz, ite_eq_right hz]

/-- The registers `topW` writes. -/
abbrev topRegs : List Reg := [.a5, .a4, .s0, .t3, .t4, .t5, .t6]

/-- `topW D`: `s0 :=` the word at `hiIdx` of the `t0 = k` words of `[D]`, every word read. -/
theorem topW_ok {s : State} {B : Addr} {Z w N D k : Nat} (h : Ws s B Z w N) (hD : D < N) (hN : N ≤ 2048)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ w) :
    WP isa (VG.Impl.Rsa.RISCV64.RecoverDet.topW D) s fun t => t.mem = s.mem ∧
      t.gpr .s0 = word s.mem B (arr w D + 8 * hiIdx (fun j => word s.mem B (arr w D + 8 * j)) k) ∧
      Keep topRegs s t := by
  have fit := h.arr_fit hD
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hwl := h.wle
  have al := arr_al w D
  have hs := h.scr
  rw [← topOf_hi (fun j => word s.mem B (arr w D + 8 * j)) hk]
  generalize hf : (fun j => word s.mem B (arr w D + 8 * j)) = f
  generalize hd : arr w D = d at fit al hf
  unfold VG.Impl.Rsa.RISCV64.RecoverDet.topW
  refine WP.seq ?_
  refine ptr_ok h (by decide) (by decide) (show D < 2048 by omega) ?_
  rw [hd]
  have hb : WP isa (.block [.li .a4 0, .li .s0 0, mov .t3 .t0]) (s.write .a5 (off B d)) fun u =>
      (u.gpr .a5 = off B d ∧ u.gpr .a4 = 0 ∧ u.gpr .s0 = 0 ∧ u.gpr .t3 = BitVec.ofNat 64 k ∧
        u.mem = s.mem) ∧ Keep [.a4, .s0, .t3] (s.write .a5 (off B d)) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    simp only [mov]
    brun [ht0, fin64_exec_li_zero, exec_addi_nat (m := 0) (by decide), BitVec.add_zero]
  refine WP.mono hb fun u ⟨⟨u5, u4, u0, u3, um⟩, uk⟩ => ?_
  have uk' : Keep topRegs s u := ((Keep.write _ _ _).trans uk).mono (by decide)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .a5 = off B (d + 8 * i) ∧ t.gpr .s0 = topOf f i ∧ t.gpr .a4 = 0 ∧ t.mem = s.mem ∧ Keep topRegs s t
  refine WP.mono (wp_countdown (cnt := .t3) (N := k) (by omega) (by omega) Inv
    (fun i hi t ⟨j5, j0, j4, jm, jk⟩ _ => ?_)
    ⟨by rw [u5]; rfl, u0, u4, um, uk'⟩ u3) fun t ⟨_, t0, _, tm, tk⟩ => ⟨tm, t0, tk⟩
  have hs' := hs.congr jk.2.2
  have wa : t.mem.readW (off B (d + 8 * i)) 64 = f i := by rw [jm, ← hf]
  refine WP.mono (WP.keep topRegs (Q := fun t' =>
      t'.gpr .a5 = off B (d + 8 * i) + BitVec.ofNat 64 8 ∧
      t'.gpr .s0 = t.gpr .s0 ^^^ ((t.gpr .s0 ^^^ f i) &&& (0 - (if f i = 0 then 0 else 1))) ∧
      t'.gpr .t3 = t.gpr .t3 - BitVec.ofNat 64 1 ∧ t'.gpr .a4 = 0 ∧ t'.mem = t.mem) (by
    brun [j5, j4, wa, bit_lt, BitVec.add_zero, exec_addi_nat (show 8 < 2048 by decide),
      hs'.ld (show d + 8 * i + 8 ≤ Z by omega), hs'.al8 (show d + 8 * i + 8 ≤ Z by omega) (by omega)])
    (by rfl) (by rfl)) fun t' ⟨⟨l5, l0, l3, l4, lm⟩, lk⟩ =>
      ⟨⟨?_, ?_, l4, by rw [lm, jm], jk.trans lk |>.mono (by decide)⟩, l3⟩
  · rw [l5, off_add, show d + 8 * i + 8 = d + 8 * (i + 1) by omega]
  · rw [l0, j0]
    have hm : (if f i = 0 then (0 : BitVec 64) else 1) = if (!decide (f i = 0)) then 1 else 0 := by
      by_cases hz : f i = 0 <;> simp [hz]
    rw [hm, selb]
    simp only [topOf]
    by_cases hz : f i = 0
    · simp [hz]
    · simp only [hz, decide_false, Bool.not_false, ite_true]
      rw [ite_eq_right not_false]

/-- `nTop`: `a1 := 0`, `t5 := 63`. -/
theorem nTop_ok (s : State) :
    WP isa (.block nTop) s fun t =>
      (t.gpr .a1 = 0 ∧ t.gpr .t5 = BitVec.ofNat 64 63 ∧ t.mem = s.mem) ∧ Keep [.a1, .t5] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [nTop, fin64_exec_li_zero, exec_li_63]

/-- `nShift`: `s8 := (64 s7 + a1) & -2` masked by `[sBb] - 1`, and half of it into `[wTmp]`'s word 1. -/
theorem nShift_ok {s : State} {B : Addr} {Z W N a z : Nat} (h : Ws s B Z W N) (hT : wTmp < N)
    (h7 : s.gpr .s7 = BitVec.ofNat 64 a) (h1 : s.gpr .a1 = BitVec.ofNat 64 z) :
    WP isa (.block nShift) s fun t =>
      (t.gpr .s8 = (BitVec.ofNat 64 (64 * a + z) &&& BitVec.ofInt 64 (-2)) &&&
          (word s.mem B sBb - BitVec.ofNat 64 1) ∧
        t.mem = s.mem.writeW (off B (arr W wTmp + 8)) (t.gpr .s8 >>> 1)) ∧
      Keep [.t2, .t3, .s8] s t := by
  have fT := h.arr_fit hT
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have alT := arr_al W wTmp
  have hs := h.scr
  unfold nShift
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t3, .s8] (Q := fun u =>
      u.gpr .s8 = (BitVec.ofNat 64 (64 * a + z) &&& BitVec.ofInt 64 (-2)) &&& (word s.mem B sBb - BitVec.ofNat 64 1) ∧
        u.gpr .t2 = u.gpr .s8 >>> 1 ∧ u.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨u8, u2, um⟩, uk⟩ => ?_
  · have hb : sBb + 8 ≤ Z := by
      have h1 := hdr_le_arr W wTmp; have h2 : hdr = 256 := hdr_eq
      simp only [sBb]; omega
    simp only [word]
    brun [h7, h1, h.s11, shl6_ofNat, add_ofNat, hs.ld (d := sBb) (n := 8) hb, hs.al8 (d := sBb) hb (by decide),
      show sBb < 2048 by decide, add_ofNat_zero']
  have hu : Ws u B Z W N := h.of_keep uk
  refine ptr1_ok hu (by decide) (by decide) (by decide) fun v v3 vk vm => ?_
  have hv := (hu.of_keep vk).scr
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = v.mem.writeW (off B (arr W wTmp + 8)) (v.gpr .t2)) ?_ (by rfl)
    (by rfl)) fun t ⟨tm, tk⟩ => ⟨⟨?_, ?_⟩, Keep.trans' (Keep.trans' (uk.mono (by decide)) (vk.mono (by decide)))
      (tk.mono (by decide))⟩
  · brun [v3, hv.st (show arr W wTmp + 8 + 8 ≤ Z by omega_arith),
      hv.al8 (show arr W wTmp + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]
  · rw [tk.gpr (by decide), vk.gpr (by decide), u8]
  · rw [tm, vm, um, vk.gpr (by decide), u2, tk.gpr (by decide), vk.gpr (by decide)]

/-- The masked even part of the leading zeros: `c₂ = 2 ⌊clz / 2⌋`, or 0 where `X = 0` (`b = 1`). -/
theorem shift_val {x : Nat} (hx : x < 2 ^ 63) {b : BitVec 64} (hb : b.toNat ≤ 1) :
    (BitVec.ofNat 64 x &&& BitVec.ofInt 64 (-2)) &&& (b - BitVec.ofNat 64 1) =
      BitVec.ofNat 64 (if b.toNat = 0 then x / 2 * 2 else 0) := by
  have e : BitVec.ofInt 64 (-2) = BitVec.allOnes 64 <<< 1 := by decide
  have ev : BitVec.ofNat 64 x &&& BitVec.ofInt 64 (-2) = BitVec.ofNat 64 (x / 2 * 2) := by
    rw [e, ← BitVec.shiftLeft_ushiftRight]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]
    omega
  rw [ev]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
  · rw [show b = 0#64 from BitVec.eq_of_toNat_eq (by rw [h0]; rfl)]
    rw [show (0#64).toNat = 0 from rfl, ite_eq_left rfl,
      show (0#64 - BitVec.ofNat 64 1) = BitVec.allOnes 64 from by decide, BitVec.and_allOnes]
  · rw [show b = 1#64 from BitVec.eq_of_toNat_eq (by rw [h1]; rfl)]
    rw [show (1#64).toNat = 1 from rfl, ite_eq_right Nat.one_ne_zero,
      show (1#64 - BitVec.ofNat 64 1) = 0#64 from by decide, BitVec.and_zero]

/-- The registers `norm` writes. -/
abbrev normRegs : List Reg :=
  [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a1, .a3, .a4, .a5, .a6, .a7, .s0, .s1, .s7, .s8]

/-- `norm` (`W` words, `4 ≤ W ≤ 260`, `[wDig]` zero): `sBb := [X = 0]`, `X := X 4^c` for `c` into `[wTmp]`'s word
1, `X 4^c ≥ 2^(64 W - 2)` where `X ≠ 0`. -/
theorem norm_ok {s : State} {B : Addr} {Z W N : Nat} (h : Ws s B Z W N) (hR : wR < N) (hDg : wDig < N)
    (hT : wTmp < N) (hN : N ≤ 2048) (hW4 : 4 ≤ W) (hW : W ≤ 260) (hZ : num s.mem B W wDig = 0) :
    WP isa norm s fun t => Ws t B Z W N ∧ Keep normRegs s t ∧ Frame B W [wR, wTmp] [sBb] s.mem t.mem ∧
      slot t.mem B sBb = (if num s.mem B W wR = 0 then 1 else 0) ∧
      ∃ c, (word t.mem B (arr W wTmp + 8)).toNat = c ∧ c ≤ 32 * W ∧
        num t.mem B W wR = num s.mem B W wR * 4 ^ c ∧
        (num s.mem B W wR ≠ 0 → 2 ^ (64 * W - 2) ≤ num s.mem B W wR * 4 ^ c) := by
  have fR := h.arr_fit hR
  have fT := h.arr_fit hT
  have nw := h.nowrap
  have hle := h.wle
  have hSz : S W = 8 * (W + 2) := rfl
  have alT := arr_al W wTmp
  unfold norm
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h (d := sBb) (a := wR) (b := wDig) hR hDg hN (by decide) (by decide))
    fun t1 ⟨h1, f1, sl1, k1⟩ => ?_
  rw [hZ] at sl1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.t0] (Q := fun u => u.gpr .t0 = BitVec.ofNat 64 W ∧ u.mem = t1.mem)
    (by brun [mov, add_ofNat_zero', h1.s9]) (by rfl) (by rfl)) fun t2 ⟨⟨t02, m2⟩, k2⟩ => ?_
  have h2 : Ws t2 B Z W N := h1.of_keep k2
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clz_ok h2 (D := wR) (k := W) hR hN t02 (by omega) (Nat.le_refl _)) fun t3 ⟨m3, s73, k3⟩ => ?_
  have h3 : Ws t3 B Z W N := h2.of_keep k3
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (topW_ok h3 (D := wR) (k := W) hR hN ((k3.gpr (by decide)).trans t02) (by omega) (Nat.le_refl _))
    fun tw ⟨mw, sw, kw⟩ => ?_
  have hw' : Ws tw B Z W N := h3.of_keep kw
  rw [m3] at sw
  obtain ⟨hi1, hi2, hi3⟩ := hiIdx_spec t2.mem B (arr W wR) W
  generalize hhi : hiIdx (fun j => word t2.mem B (arr W wR + 8 * j)) W = hi at s73 hi1 hi2 hi3 sw
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (nTop_ok tw) fun t4 ⟨⟨a14, t54, m4'⟩, k4⟩ => ?_
  have h4 : Ws t4 B Z W N := hw'.of_keep k4
  have m4 : t4.mem = t3.mem := m4'.trans mw
  have s04 : t4.gpr .s0 = word t3.mem B (arr W wR + 8 * hi) := by rw [k4.gpr (by decide), sw, m3]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (wp_countdown (body := .block (lzStep ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := 63)
    (by decide) (by decide) (LzI t4 (t4.gpr .s0).toNat) (fun j _ t hI _ => lzStep_ok hI)
    ⟨0, by simp, by rw [a14]; rfl, Nat.le_refl _, fun h => absurd h (by decide), rfl, Keep.refl _ _⟩ t54)
    fun t5 ⟨z, hz0, hz1, hz2, hz3, hz4, hz5⟩ => ?_
  have h5 : Ws t5 B Z W N := h4.of_keep hz5
  -- The words read, and the top word `T`.
  have mX : wordsVal t2.mem B (arr W wR) W = num s.mem B W wR := by
    rw [m2]; exact f1.num (by simp) (by intro d hd; simp at hd; subst hd; decide) (h.fit64 hR)
  rw [mX] at hi2 hi3
  have hT' : (t4.gpr .s0).toNat = num s.mem B W wR / 2 ^ (64 * hi) := by
    have hhi' : hi < W := by omega
    rw [s04, m3, top_word_div (mm := t2.mem) (B := B) (p := arr W wR) (W := W) (hi := hi) hhi' (by rw [mX]; exact hi2),
      mX]
  -- The top word, normalized: `2^63 ≤ T 2^z`.
  have h1v : num s.mem B W wR ≠ 0 → 2 ^ 63 ≤ (t4.gpr .s0).toNat * 2 ^ z := fun hX0 => by
    rcases Nat.lt_or_ge z 63 with c | c
    · exact hz3 c
    · have hz63 : z = 63 := by omega
      have hT1 : 1 ≤ (t4.gpr .s0).toNat := by
        rw [hT', Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.one_mul]; exact hi3 (Nat.pos_of_ne_zero hX0)
      rw [hz63]; exact Nat.le_mul_of_pos_left _ hT1
  have hs7 : t5.gpr .s7 = BitVec.ofNat 64 (W - 1 - hi) := by
    rw [hz5.gpr (by decide), k4.gpr (by decide), kw.gpr (by decide), s73]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (nShift_ok h5 hT hs7 hz1) fun t6 ⟨⟨s86, m6⟩, k6⟩ => ?_
  have h6 : Ws t6 B Z W N := h5.of_keep k6
  -- The slot `sBb`, as `eqS` left it.
  have sb5 : word t5.mem B sBb = word t1.mem B sBb := by rw [hz4, m4, m3, m2]
  have hsb : (word t5.mem B sBb).toNat ≤ 1 := by
    rw [sb5]; show slot t1.mem B sBb ≤ 1; rw [sl1]; split <;> omega
  have hclz : 64 * (W - 1 - hi) + z < 2 ^ 63 := by omega
  rw [shift_val hclz hsb, sb5] at s86
  have sl1' : (word t1.mem B sBb).toNat = if num s.mem B W wR = 0 then 1 else 0 := sl1
  rw [sl1'] at s86
  generalize hc2 : (if (if num s.mem B W wR = 0 then 1 else 0) = 0 then (64 * (W - 1 - hi) + z) / 2 * 2 else 0) =
    c2 at s86
  have hcl : 64 * (W - 1 - hi) + z < 64 * W := by have := hz2; omega
  have c2l : c2 < 64 * W := by
    rw [← hc2]
    by_cases c : (if num s.mem B W wR = 0 then 1 else 0) = 0
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_right c]; omega
  have c2e : c2 % 2 = 0 := by
    rw [← hc2]
    by_cases c : (if num s.mem B W wR = 0 then 1 else 0) = 0
    · rw [ite_eq_left c]; omega
    · rw [ite_eq_right c]
  rw [seqs_one]
  refine WP.mono (shlBy_ok h6 (X := wR) (R := .s8) (r := c2) (n := 9) hR hN s86 (by decide) (by omega) (by decide)
    (by omega) (by omega)) fun t ⟨h7, f7, v7, k7⟩ => ?_
  refine ⟨h7, ?_, ?_, ?_, c2 / 2, ?_, by omega, ?_, ?_⟩
  · exact Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (Keep.trans' (k1.mono (by decide))
      (k2.mono (by decide))) (Keep.trans' (k3.mono (by decide)) (kw.mono (by decide)))) (k4.mono (by decide)))
      (hz5.mono (by decide)))
      (k6.mono (by decide))) (k7.mono (by decide))
  · have f6 : Frame B W [wR, wTmp] [sBb] t5.mem t6.mem := by
      rw [m6, show arr W wTmp + 8 = arr W wTmp + 8 from rfl]
      exact Frame.of_arr (o := wTmp) (d := 8) (writeW_outside _ _ _ (by omega_arith)) (by omega) (by simp)
    have e15 : t5.mem = t1.mem := by rw [hz4, m4, m3, m2]
    rw [← e15] at f1
    exact ((f1.mono (by simp) (by simp)).trans f6).trans (f7.mono (by simp) (by simp))
  · have := f7.slot (e := sBb) (by decide) (by simp)
    show (word t.mem B sBb).toNat = _
    rw [show (word t.mem B sBb).toNat = slot t.mem B sBb from rfl, this]
    show (word t6.mem B sBb).toNat = _
    have hb' : sBb + 8 ≤ arr W wTmp + 8 := by
      have h1 := hdr_le_arr W wTmp; have h2 : hdr = 256 := hdr_eq; simp only [sBb]; omega
    rw [m6, (writeW_outside _ B _ (by omega_arith)).word (.inl hb') (by omega_arith), sb5]
    exact sl1'
  · have w8 : word t.mem B (arr W wTmp + 8) = word t6.mem B (arr W wTmp + 8) := by
      have dRT := arr_disj (w := W) (show wR ≠ wTmp by decide)
      have := f7.words (d := arr W wTmp + 8) (k := 1) (fun k hk => by simp at hk; subst hk; omega) (by simp)
        (by omega_arith)
      apply BitVec.eq_of_toNat_eq; simpa [wordsVal] using this
    rw [w8, m6, word_writeW_self, s86, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega)]
  · -- `X 2^c₂`, exactly.
    have dRT := arr_disj (w := W) (show wR ≠ wTmp by decide)
    have X6 : wordsVal t6.mem B (arr W wR) W = num s.mem B W wR := by
      rw [m6, (writeW_outside _ B _ (by omega_arith)).wordsVal (by omega) (by omega_arith), hz4, m4, m3, ← mX]
    show wordsVal t.mem B (arr W wR) W = _
    rw [v7, X6]
    have e4 : 4 ^ (c2 / 2) = 2 ^ c2 := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega
    rw [e4]
    by_cases hX0 : num s.mem B W wR = 0
    · rw [hX0]; simp
    · have hc2' : c2 = (64 * (W - 1 - hi) + z) / 2 * 2 := by rw [← hc2, ite_eq_right hX0, ite_eq_left rfl]
      refine Nat.mod_eq_of_lt ?_
      rw [hc2']
      exact (norm_bounds hT' (by omega) hz2 (h1v hX0) (by rw [← hz0]; exact (t5.gpr .s0).isLt)).2
  · intro hX0
    have hc2' : c2 = (64 * (W - 1 - hi) + z) / 2 * 2 := by rw [← hc2, ite_eq_right hX0, ite_eq_left rfl]
    have e4 : 4 ^ (c2 / 2) = 2 ^ c2 := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]; congr 1; omega
    rw [e4, hc2']
    exact (norm_bounds hT' (by omega) hz2 (h1v hX0) (by rw [← hz0]; exact (t5.gpr .s0).isLt)).1

/-! ## The square root -/

/-- The top two words of `W` words: `⌊X / β^(W - 2)⌋`. -/
theorem top2 (mm : Mem) (B : Addr) (p W : Nat) (hW : 2 ≤ W) :
    v2 (word mm B (p + 8 * W - 16 + 8)) (word mm B (p + 8 * W - 16)) = wordsVal mm B p W / 2 ^ (64 * (W - 2)) := by
  have e := wordsVal_append mm B p (W - 2) 2
  rw [show W - 2 + 2 = W by omega] at e
  have e2 : wordsVal mm B (p + 8 * (W - 2)) 2 = v2 (word mm B (p + 8 * W - 16 + 8)) (word mm B (p + 8 * W - 16)) := by
    simp only [wordsVal, v2]
    rw [show p + 8 * (W - 2) = p + 8 * W - 16 by omega]
    omega
  rw [e, e2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (wordsVal_lt _ _ _ _), Nat.zero_add]

/-- After `first`: `DV` with one digit, its root `y` and remainder `r1:r0` over `[wR]`'s top two words, the root
into `[wSN]` (zero), from `[wR] = Xn`. -/
theorem dv_first {mm : Mem} {B : Addr} {W k Xn : Nat} {r1 r0 y v : BitVec 64} (hk : W = 2 * k) (hk2 : 2 ≤ k)
    (fitR : arr W wR + S W ≤ 2 ^ 64) (fitS : arr W wSN + S W ≤ 2 ^ 64) (fitT : arr W wTmp + S W ≤ 2 ^ 64)
    (hX : wordsVal mm B (arr W wR) W = Xn) (hS0 : wordsVal mm B (arr W wSN) W = 0)
    (hy : y.toNat = isqrt (v2 (word mm B (arr W wR + 8 * W - 16 + 8)) (word mm B (arr W wR + 8 * W - 16))))
    (hr : v2 r1 r0 + y.toNat * y.toNat = v2 (word mm B (arr W wR + 8 * W - 16 + 8)) (word mm B (arr W wR + 8 * W - 16))) :
    DV ((((mm.writeW (off B (arr W wR + 8 * W - 16)) r0).writeW (off B (arr W wR + 8 * W - 16 + 8)) r1).writeW
      (off B (arr W wSN + 8 * (W / 2) - 8)) y).writeW (off B (arr W wTmp)) v) B W k 1 Xn y.toNat := by
  have hSz : S W = 8 * (W + 2) := rfl
  have dRS := arr_disj (w := W) (show wR ≠ wSN by decide)
  have dRT := arr_disj (w := W) (show wR ≠ wTmp by decide)
  have dST := arr_disj (w := W) (show wSN ≠ wTmp by decide)
  rw [top2 mm B _ W (by omega), hX] at hy hr
  have hk' : W / 2 = k := by omega
  rw [hk']
  -- The writes, each outside the others' regions.
  have o0 := writeW_outside mm B (d := arr W wR + 8 * W - 16) r0 (by omega)
  generalize m1e : mm.writeW (off B (arr W wR + 8 * W - 16)) r0 = m1 at o0
  have o1 := writeW_outside m1 B (d := arr W wR + 8 * W - 16 + 8) r1 (by omega)
  generalize m2e : m1.writeW (off B (arr W wR + 8 * W - 16 + 8)) r1 = m2 at o1
  have o2 := writeW_outside m2 B (d := arr W wSN + 8 * k - 8) y (by omega)
  generalize m3e : m2.writeW (off B (arr W wSN + 8 * k - 8)) y = m3 at o2
  have o3 := writeW_outside m3 B (d := arr W wTmp) v (by omega)
  generalize m4e : m3.writeW (off B (arr W wTmp)) v = m4 at o3
  refine ⟨y.toNat, v2 r1 r0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `[wSN]`: zero but `y` at word `k - 1`.
    rw [o3.wordsVal (by omega) (by omega)]
    rw [← m3e, show arr W wSN + 8 * k - 8 = arr W wSN + 8 * (k - 1) by omega]
    have w0 : word m2 B (arr W wSN + 8 * (k - 1)) = 0 := by
      rw [o1.word (by omega) (by omega), o0.word (by omega) (by omega)]
      have := wordsVal_zero_part hS0 (a := k - 1) (c := 1) (by omega)
      apply BitVec.eq_of_toNat_eq; simpa [wordsVal] using this
    rw [wv_write_zero y w0 (by omega) (by omega), o1.wordsVal (by omega) (by omega), o0.wordsVal (by omega) (by omega),
      hS0, Nat.zero_add, Nat.mul_comm]
  · simp
  · -- The low words.
    rw [show W - 2 * 1 = W - 2 by omega, o3.wordsVal (by omega) (by omega), o2.wordsVal (by omega) (by omega),
      o1.wordsVal (by omega) (by omega), o0.wordsVal (by omega) (by omega)]
    have := wordsVal_mod_low mm B (arr W wR) (W - 2) 2
    rw [show W - 2 + 2 = W by omega, hX] at this
    exact this.symm
  · -- The remainder over the top two words.
    have wa : word m4 B (arr W wR + 8 * W - 16 + 8) = r1 := by
      rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), ← m2e, word_writeW_self]
    have wb : word m4 B (arr W wR + 8 * W - 16) = r0 := by
      rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega), ← m1e,
        word_writeW_self]
    rw [show W - 2 * 1 = W - 2 by omega, show 2 * 1 = 2 from rfl]
    simp only [wordsVal]
    rw [show arr W wR + 8 * (W - 2) = arr W wR + 8 * W - 16 by omega, wa, wb]
    simp only [v2]
    omega
  · -- `r ≤ 2 y`.
    have := lt_succ_isqrt_sq (Xn / 2 ^ (64 * (W - 2)))
    rw [← hy] at this
    have e : (y.toNat + 1) * (y.toNat + 1) = y.toNat * y.toNat + 2 * y.toNat + 1 := by ring
    omega
  · rw [show W - 2 * 1 = W - 2 by omega, Nat.add_comm]; exact hr

theorem or_bits {x y : BitVec 64} (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ||| y).toNat = if x.toNat = 1 ∨ y.toNat = 1 then 1 else 0 := by
  rw [BitVec.toNat_or]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with h0 | h0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hy with h1 | h1 <;> rw [h0, h1] <;> rfl

/-- `sOk5 := sOk5 | sBb`. -/
theorem okOr_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) :
    WP isa (.block [.load .d .t2 .s11 sOk5, .load .d .t3 .s11 sBb, .logic .or .t2 .t2 .t3, .store .d .t2 .s11 sOk5]) s
      fun t => (t.mem = s.mem.writeW (off B sOk5) (word s.mem B sOk5 ||| word s.mem B sBb)) ∧ Keep [.t2, .t3] s t := by
  have nw := h.nowrap
  have hz := h.hdr_le
  simp only [hdr_eq] at hz
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h.s11, h.scr.st (d := sOk5) (n := 8) (by simp only [sOk5]; omega_arith),
    h.scr.al8 (d := sOk5) (by simp only [sOk5]; omega_arith) (by decide),
    h.scr.ld (d := sOk5) (n := 8) (by simp only [sOk5]; omega_arith),
    h.scr.ld (d := sBb) (n := 8) (by simp only [sBb]; omega_arith),
    h.scr.al8 (d := sBb) (by simp only [sBb]; omega_arith) (by decide),
    show sOk5 < 2048 by decide, show sBb < 2048 by decide, add_ofNat_zero']

/-- `s8 :=` `[wTmp]`'s word 1. -/
theorem ldC_ok {s : State} {B : Addr} {Z W N : Nat} (h : Ws s B Z W N) (hT : wTmp < N) :
    WP isa (.block (ptr .t3 wTmp ++ ([.load .d .s8 .t3 8] : List Instr))) s fun t =>
      (t.gpr .s8 = word s.mem B (arr W wTmp + 8) ∧ t.mem = s.mem) ∧ Keep [.t3, .s8] s t := by
  have fT := h.arr_fit hT
  have nw := h.nowrap
  have hSz : S W = 8 * (W + 2) := rfl
  have alT := arr_al W wTmp
  refine ptr1_ok h (by decide) (by decide) (by decide) fun u u3 uk um => ?_
  have hu := (h.of_keep uk).scr
  refine WP.mono (WP.keep [.s8] (Q := fun t => t.gpr .s8 = word s.mem B (arr W wTmp + 8) ∧ t.mem = s.mem) ?_
    (by rfl) (by rfl)) fun t ⟨q, k⟩ => ⟨q, Keep.trans' (uk.mono (by decide)) (k.mono (by decide))⟩
  rw [← um]
  simp only [word]
  brun [u3, hu.ld (show arr W wTmp + 8 + 8 ≤ Z by omega_arith),
    hu.al8 (show arr W wTmp + 8 + 8 ≤ Z by omega_arith) (by omega_arith)]

/-- A word outside a frame's arrays and slots. -/
theorem frame_word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem} (f : Frame B w js ds m m') {e : Nat}
    (hj : ∀ j ∈ js, e + 8 ≤ arr w j ∨ arr w j + S w ≤ e) (hd : ∀ d ∈ ds, e + 8 ≤ d ∨ d + 8 ≤ e)
    (fit : e + 8 ≤ 2 ^ 64) : word m' B e = word m B e := by
  have := f.words (d := e) (k := 1) (by simpa using hj) (by simpa using hd) (by simpa using fit)
  apply BitVec.eq_of_toNat_eq; simpa [wordsVal] using this

/-- A word written in array `o`. -/
theorem frame_write {mm : Mem} {B : Addr} {W o d e : Nat} {js : List Nat} (val : BitVec 64) (hd : d + 8 ≤ S W)
    (he : arr W o + d = e) (fit : arr W o + S W ≤ 2 ^ 64) (ho : o ∈ js) :
    Frame B W js [] mm (mm.writeW (off B e) val) := by
  subst he
  exact Frame.of_arr (writeW_outside mm B val (by omega)) hd ho

/-- `first`'s writes, in `[wR]`, `[wSN]` and `[wTmp]`. -/
theorem frame_first {mm : Mem} {B : Addr} {W : Nat} {r1 r0 y v : BitVec 64} (hW : 2 ≤ W)
    (fitR : arr W wR + S W ≤ 2 ^ 64) (fitS : arr W wSN + S W ≤ 2 ^ 64) (fitT : arr W wTmp + S W ≤ 2 ^ 64) :
    Frame B W [wR, wSN, wTmp] [] mm ((((mm.writeW (off B (arr W wR + 8 * W - 16)) r0).writeW
      (off B (arr W wR + 8 * W - 16 + 8)) r1).writeW (off B (arr W wSN + 8 * (W / 2) - 8)) y).writeW
      (off B (arr W wTmp)) v) := by
  have hSz : S W = 8 * (W + 2) := rfl
  exact (((frame_write r0 (d := 8 * W - 16) (by omega) (by omega) fitR (by simp)).trans
    (frame_write r1 (d := 8 * W - 16 + 8) (by omega) (by omega) fitR (by simp))).trans
    (frame_write y (d := 8 * (W / 2) - 8) (by omega) (by omega) fitS (by simp))).trans
    (frame_write v (d := 0) (by omega) (by omega) fitT (by simp))

/-- The root and remainder of the normalized radicand give those of the radicand. -/
theorem sqrt_vals {Sv R X c : Nat} (h : Sv * Sv + R = X * 4 ^ c) (hR : R ≤ 2 * Sv) :
    Sv / 2 ^ c = isqrt X ∧ (R = 0 ↔ isqrt X * isqrt X = X) := by
  rw [Nat.mul_comm X] at h
  have e := VG.Proof.Bignum.SqrtRem.sqrt_of_rem h hR
  refine ⟨by rw [← e]; exact VG.Proof.Bignum.SqrtRem.norm_sqrt c X, ?_⟩
  rw [← VG.Proof.Bignum.SqrtRem.norm_square c X]
  exact (VG.Proof.Bignum.SqrtRem.square_iff_rem h hR).symm

/-- After every digit: the root in `[wSN]`, the remainder in `[wR]`. -/
theorem dv_last {mm : Mem} {B : Addr} {W k Xn d0 : Nat} (hk : W = 2 * k) (h : DV mm B W k k Xn d0) :
    ∃ Sv R, wordsVal mm B (arr W wSN) W = Sv ∧ wordsVal mm B (arr W wR) W = R ∧ R ≤ 2 * Sv ∧
      Sv * Sv + R = Xn := by
  obtain ⟨Sv, R, h1, _, _, h4, h5, h6⟩ := h
  have z : W - 2 * k = 0 := by omega
  rw [Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at h1
  rw [z, Nat.mul_zero, Nat.add_zero, ← hk] at h4
  rw [z, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h6
  exact ⟨Sv, R, h1, h4, h5, h6⟩

/-- The root's shift, `[wTmp]`'s word 1, through `first`, `digits`, `eqS` and the `or`. -/
theorem word_tmp_keep {B : Addr} {W : Nat} {m4 m6 m7 : Mem} {r0 r1 y v : BitVec 64} (hW : 2 ≤ W)
    (fR : arr W wR + S W ≤ 2 ^ 64) (fS : arr W wSN + S W ≤ 2 ^ 64) (fT : arr W wTmp + S W ≤ 2 ^ 64)
    (f6 : Frame B W [wR, wSN] [] ((((m4.writeW (off B (arr W wR + 8 * W - 16)) r0).writeW
      (off B (arr W wR + 8 * W - 16 + 8)) r1).writeW (off B (arr W wSN + 8 * (W / 2) - 8)) y).writeW
      (off B (arr W wTmp)) v) m6)
    (f7 : Frame B W [] [sOk5] m6 m7) :
    word (m7.writeW (off B sOk5) (word m7 B sOk5 ||| word m7 B sBb)) B (arr W wTmp + 8) =
      word m4 B (arr W wTmp + 8) := by
  have hTh := hdr_le_arr W wTmp
  have hhdr : hdr = 256 := hdr_eq
  have aTS : arr W wTmp + S W ≤ arr W wSN := arr_end (by decide)
  have aSR : arr W wSN + S W ≤ arr W wR := arr_end (by decide)
  have hSz : S W = 8 * (W + 2) := rfl
  rw [(writeW_outside m7 B (d := sOk5) _ (by decide)).word (d := arr W wTmp + 8) (.inr (by simp only [sOk5]; omega))
      (by omega),
    frame_word f7 (e := arr W wTmp + 8) (by simp) (by simp only [List.mem_singleton, forall_eq, sOk5]; omega) (by omega),
    frame_word f6 (e := arr W wTmp + 8)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega) (by simp) (by omega),
    (writeW_outside _ B (d := arr W wTmp) _ (by omega)).word (d := arr W wTmp + 8) (.inr (by omega)) (by omega),
    (writeW_outside _ B (d := arr W wSN + 8 * (W / 2) - 8) _ (by omega)).word (d := arr W wTmp + 8) (.inl (by omega))
      (by omega),
    (writeW_outside _ B (d := arr W wR + 8 * W - 16 + 8) _ (by omega)).word (d := arr W wTmp + 8) (.inl (by omega))
      (by omega),
    (writeW_outside _ B (d := arr W wR + 8 * W - 16) _ (by omega)).word (d := arr W wTmp + 8) (.inl (by omega))
      (by omega)]

/-- `sqrt` on the wide view (`W = 2 w + 2` words): `[aSy] := ⌊√X⌋ mod 2^(64 w)` (narrow) for `X = [wR]`, and
`sOk5 := [⌊√X⌋² = X]`. -/
theorem sqrt_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z (W2 w) 31) (hfit : arr w 63 ≤ Z)
    (hw : 1 ≤ w) (hw' : w ≤ 129) (hZ0 : num s.mem B w aZero = 0) :
    WP isa sqrt s fun t => Ws t B Z w 63 ∧
      Frame B w (aSy :: halves [wR, wSN, wDig, wTmp]) (sBb :: sOk5 :: divSlots) s.mem t.mem ∧ Keep dvRegs s t ∧
      num t.mem B w aSy = isqrt (num s.mem B (W2 w) wR) % 2 ^ (64 * w) ∧
      slot t.mem B sOk5 =
        (if isqrt (num s.mem B (W2 w) wR) * isqrt (num s.mem B (W2 w) wR) = num s.mem B (W2 w) wR then 1 else 0) := by
  have fR := h.fit64 (show wR < 31 by decide)
  have fS := h.fit64 (show wSN < 31 by decide)
  have fT := h.fit64 (show wTmp < 31 by decide)
  have fD := h.fit64 (show wDig < 31 by decide)
  have nw := h.nowrap
  have hSz : S (W2 w) = 8 * (W2 w + 2) := rfl
  generalize hX : num s.mem B (W2 w) wR = X
  unfold sqrt
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (saveDiv_ok h) fun t1 ⟨h1, f1, k1, sv1, sv2, sv3, sv4, sv5, sv6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h1 (j := wSN) (by decide) (by decide)) fun t2 ⟨h2, f2, z2, k2⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (zeroW1_ok h2 (j := wDig) (by decide) (by decide)) fun t3 ⟨h3, f3, z3, k3⟩ => ?_
  have zD3 : num t3.mem B (W2 w) wDig = 0 := (wv_prefix (a := W2 w) (b := 1) z3 (Nat.two_pow_pos _)).1
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (norm_ok h3 (by decide) (by decide) (by decide) (by decide) (by simp only [W2]; omega)
    (by simp only [W2]; omega) zD3) fun t4 ⟨h4, k4, f4, sb4, c, hc4, hcl, hn4, hlo4⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (first_ok h4 (by decide) (by decide) (by decide) (by simp only [W2]; omega))
    fun t5 ⟨h5, k5, s75, r1, r0, y, v, m5, hy, hr, hv⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (digits_ok (k := w + 1) h5 (by decide) (by decide) (by decide) (by simp only [W2]; omega) (by omega) s75)
    fun t6 ⟨h6, k6, f6, dv6⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (eqS_ok h6 (d := sOk5) (a := wR) (b := wDig) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t7 ⟨h7, f7, ok7, k7⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (okOr_ok h7) fun t8 ⟨m8, k8⟩ => ?_
  have h8 : Ws t8 B Z (W2 w) 31 := h7.of_keep k8
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ldC_ok h8 (show wTmp < 31 by decide)) fun t9 ⟨⟨s89, m9⟩, k9⟩ => ?_
  have h9 : Ws t9 B Z (W2 w) 31 := h8.of_keep k9
  have alT := arr_al (W2 w) wTmp
  have alS := arr_al (W2 w) wSN
  have dRS := arr_disj (w := W2 w) (show wR ≠ wSN by decide)
  have dRT := arr_disj (w := W2 w) (show wR ≠ wTmp by decide)
  have dST := arr_disj (w := W2 w) (show wSN ≠ wTmp by decide)
  have hdT := hdr_le_arr (W2 w) wDig
  have hW2 : W2 w = 2 * (w + 1) := by simp only [W2]; omega
  -- The frames, in the wide view.
  have f5 : Frame B (W2 w) [wR, wSN, wTmp] [] t4.mem t5.mem := by
    rw [m5]; exact frame_first (by omega) fR fS fT
  have f8 : Frame B (W2 w) [] [sOk5] t7.mem t8.mem := by
    rw [m8]; exact (slot_write _ (by decide)).1
  -- `[wR]` into `norm`, and `[wSN]` zero.
  have F13 : Frame B (W2 w) [wSN, wDig] divSlots s.mem t3.mem :=
    ((f1.mono (by simp) (by simp)).trans (f2.mono (by simp) (by simp))).trans (f3.mono (by simp) (by simp))
  have X3 : num t3.mem B (W2 w) wR = X := by
    rw [← hX]; exact F13.num (by decide) divSlots_le fR
  rw [X3] at hn4 hlo4 sb4
  have S4 : wordsVal t4.mem B (arr (W2 w) wSN) (W2 w) = 0 := by
    have z2' : num t2.mem B (W2 w) wSN = 0 := (wv_prefix (a := W2 w) (b := 1) z2 (Nat.two_pow_pos _)).1
    have := ((f3.mono (js' := [wDig, wR, wTmp]) (ds' := [sBb]) (by simp) (by simp)).trans
      (f4.mono (js' := [wDig, wR, wTmp]) (ds' := [sBb]) (by simp) (by simp))).num (j := wSN) (by decide) (by decide) fS
    exact this.trans z2'
  -- The digits' invariant, after `first`.
  have hk : W2 w / 2 = w + 1 := by omega
  have o5a : ∀ e, e + 8 ≤ arr (W2 w) wTmp ∨ arr (W2 w) wTmp + 8 ≤ e → e + 8 ≤ 2 ^ 64 →
      word t5.mem B e = word ((((t4.mem.writeW (off B (arr (W2 w) wR + 8 * W2 w - 16)) r0).writeW
        (off B (arr (W2 w) wR + 8 * W2 w - 16 + 8)) r1).writeW (off B (arr (W2 w) wSN + 8 * (W2 w / 2) - 8)) y)) B e :=
    fun e he he' => by rw [m5]; exact (writeW_outside _ B v (by omega)).word he he'
  have y5 : word t5.mem B (arr (W2 w) wSN + 8 * (w + 1) - 8) = y := by
    rw [o5a _ (by omega) (by omega), ← hk, word_writeW_self]
  have v5 : word t5.mem B (arr (W2 w) wTmp) = v := by rw [m5, word_writeW_self]
  have hT2 : v2 (word t4.mem B (arr (W2 w) wR + 8 * W2 w - 16 + 8)) (word t4.mem B (arr (W2 w) wR + 8 * W2 w - 16)) =
      X * 4 ^ c / 2 ^ (64 * (W2 w - 2)) := by rw [top2 _ _ _ _ (by omega)]; exact congrArg (· / _) hn4
  have DV1 := dv_first (mm := t4.mem) (B := B) (v := v) hW2 (by omega) fR fS fT hn4 S4 hy hr
  rw [← m5] at DV1
  rw [hT2] at hy hr
  -- The value, where `X ≠ 0`: `y ≥ 2^63`, and the digits' invariant after all of them.
  have hDVk : X ≠ 0 → DV t6.mem B (W2 w) (w + 1) (w + 1) (X * 4 ^ c) y.toNat := fun hX0 => by
    have h63 : 2 ^ 63 ≤ y.toNat := by
      rw [hy]
      refine le_isqrt ?_
      have : 2 ^ 126 ≤ X * 4 ^ c / 2 ^ (64 * (W2 w - 2)) := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
        exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (hlo4 hX0)
      exact Nat.le_trans (by decide) this
    have := dv6 (X * 4 ^ c) (by rw [y5]; exact h63) (by rw [y5, v5]; exact hv h63) (by rw [y5]; exact DV1)
    rw [y5] at this
    exact this
  -- `c` and the root's shift.
  have hTh := hdr_le_arr (W2 w) wTmp
  have hhdr : hdr = 256 := hdr_eq
  have aTS : arr (W2 w) wTmp + S (W2 w) ≤ arr (W2 w) wSN := arr_end (by decide)
  have aSR : arr (W2 w) wSN + S (W2 w) ≤ arr (W2 w) wR := arr_end (by decide)
  have c8 : word t8.mem B (arr (W2 w) wTmp + 8) = word t4.mem B (arr (W2 w) wTmp + 8) := by
    rw [m8]; exact word_tmp_keep (by omega) fR fS fT (by rw [← m5]; exact f6) f7
  have hc9 : t9.gpr .s8 = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    rw [s89, c8, hc4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [W2] at hcl; omega)]
  -- The root down by `c`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (shrBy_ok h9 (X := wSN) (R := .s8) (r := c) (n := 8) (by decide) (by decide) hc9 (by decide)
    (show c < 16384 by simp only [W2] at hcl; omega) (by decide) (by omega) (by omega))
    fun t10 ⟨h10, f10, v10, k10⟩ => ?_
  -- The borrowed registers back.
  have mo : ∀ {js ds : List Nat} {m m' : Mem}, Frame B (W2 w) js ds m m' →
      (∀ j ∈ js, j ∈ [wR, wSN, wDig, wTmp]) → (∀ d ∈ ds, d ∈ sBb :: sOk5 :: divSlots) →
      Frame B (W2 w) [wR, wSN, wDig, wTmp] (sBb :: sOk5 :: divSlots) m m' := fun f hj hd => f.mono hj hd
  have mo' : ∀ {js ds : List Nat} {m m' : Mem}, Frame B (W2 w) js ds m m' →
      (∀ j ∈ js, j ∈ [wR, wSN, wDig, wTmp]) → (∀ d ∈ ds, d ∈ [sBb, sOk5]) →
      Frame B (W2 w) [wR, wSN, wDig, wTmp] [sBb, sOk5] m m' := fun f hj hd => f.mono hj hd
  have F110 : Frame B (W2 w) [wR, wSN, wDig, wTmp] [sBb, sOk5] t1.mem t10.mem := by
    rw [m9] at f10
    exact (((((((mo' f2 (by decide) (by decide)).trans (mo' f3 (by decide) (by decide))).trans
      (mo' f4 (by decide) (by decide))).trans (mo' f5 (by decide) (by decide))).trans
      (mo' f6 (by decide) (by decide))).trans (mo' f7 (by decide) (by decide))).trans
      (mo' f8 (by decide) (by decide))).trans (mo' f10 (by decide) (by decide))
  have FW : Frame B (W2 w) [wR, wSN, wDig, wTmp] (sBb :: sOk5 :: divSlots) s.mem t10.mem :=
    (mo f1 (by decide) (by decide)).trans (mo F110 (by decide) (by decide))
  have sw : ∀ e, e + 8 ≤ 232 → word t10.mem B e = word t1.mem B e := fun e he =>
    frame_word F110 (fun j _ => .inl (Nat.le_trans (by rw [hhdr]; omega) (hdr_le_arr _ _)))
      (fun d hd => .inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl <;> simp only [sBb, sOk5] <;> omega)) (by omega)
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (restDiv_ok h10 ((sw _ (by decide)).trans sv1) ((sw _ (by decide)).trans sv2)
    ((sw _ (by decide)).trans sv3) ((sw _ (by decide)).trans sv4) ((sw _ (by decide)).trans sv5)
    ((sw _ (by decide)).trans sv6)) fun t11 ⟨⟨g1, g2, g3, g4, g5, g6, m11⟩, k11⟩ => ?_
  have h11 := h10.of_keep k11
  have K10 : Keep (dvRegs ++ [.s1, .s2, .s3, .s4, .a0, .a1]) s t10 :=
    Keep.trans' (k1.mono (by decide)) (Keep.trans' (k2.mono (by decide)) (Keep.trans' (k3.mono (by decide))
      (Keep.trans' (k4.mono (by decide)) (Keep.trans' (k5.mono (by decide)) (Keep.trans' (k6.mono (by decide))
      (Keep.trans' (k7.mono (by decide)) (Keep.trans' (k8.mono (by decide)) (Keep.trans' (k9.mono (by decide))
      (k10.mono (by decide))))))))))
  have K11 : Keep dvRegs s t11 := keep_restored K10 k11 g1 g2 g3 g4 g5 g6
  -- The narrow view, the root's low words, and the zero root where `X = 0`.
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ctxw_ok (N := 63) h11 (by omega) hfit) fun t12 ⟨⟨h12, m12⟩, k12⟩ => ?_
  have fitN : ∀ j < 63, arr w j + S w ≤ 2 ^ 64 := fun j hj => h12.fit64 hj
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (copy_ok h12 (o := aSy) (a := 2 * wSN) (by decide) (by decide) (by decide) (by decide))
    fun t13 ⟨h13, f13, v13, k13, _⟩ => ?_
  -- The slots.
  have sB7 : slot t7.mem B sBb = if X = 0 then 1 else 0 := by
    rw [f7.slot (by decide) (by decide), f6.slot (by decide) (by simp), f5.slot (by decide) (by simp), sb4]
  have sB13 : slot t13.mem B sBb = if X = 0 then 1 else 0 := by
    rw [f13.slot (by decide) (by simp), m12, m11, f10.slot (by decide) (by simp), m9,
      f8.slot (by decide) (by decide), sB7]
  have aB : Ahead (arr w aSy) (arr w aZero) w := by
    simpa using ahead_of_ne (w := w) (o := aSy) (a := aZero) (by decide) 0 (by decide)
  refine WP.mono (sel_gen_ok h13 (o := aSy) (a := aSy) (b := aZero) (sl := sBb) (by decide) (by decide)
    (by decide) (by decide) (ahead_self _ _ _) aB (by decide) (by decide) (by rw [sB13]; split <;> decide))
    fun t ⟨h14, f14, v14, k14⟩ => ?_
  refine ⟨h14, ?_, Keep.trans' K11 (Keep.trans' (k12.mono (by decide)) (Keep.trans' (k13.mono (by decide))
    (k14.mono (by decide)))), ?_, ?_⟩
  · rw [← m11, ← m12] at FW
    exact (FW.toNarrow.mono (by decide) (by simp)).trans ((f13.mono (by simp) (by simp)).trans
      (f14.mono (by simp) (by simp)))
  · rw [v14, sB13]
    by_cases hX0 : X = 0
    · simp only [hX0, ↓reduceIte, Nat.one_ne_zero]
      rw [f13.num (by decide) (by simp) (fitN _ (by decide)), m12, m11,
        FW.toNarrow.num (by decide) (by decide) (fitN _ (by decide)), hZ0, isqrt_zero, Nat.zero_mod]
    · simp only [hX0, ↓reduceIte]
      obtain ⟨Sv, R, eS, _, hR, hSR⟩ := dv_last (by omega) (hDVk hX0)
      have N9 : wordsVal t9.mem B (arr (W2 w) wSN) (W2 w) = Sv := by
        rw [m9]
        change num t8.mem B (W2 w) wSN = Sv
        rw [f8.num (by simp) (by decide) fS, f7.num (by simp) (by decide) fS]
        exact eS
      rw [v13, m12, m11]
      change wordsVal t10.mem B (arr w (2 * wSN)) w = _
      rw [← arr_W2, ← wordsVal_mod_low t10.mem B _ w (w + 2), show w + (w + 2) = W2 w by simp only [W2]; omega,
        v10, N9, (sqrt_vals hSR hR).1]
  · rw [f14.slot (by decide) (by simp), f13.slot (by decide) (by simp), m12, m11, f10.slot (by decide) (by simp), m9,
      m8, (slot_write (w := W2 w) _ (by decide)).2]
    have o7 : (word t7.mem B sOk5).toNat = if num t6.mem B (W2 w) wR = num t6.mem B (W2 w) wDig then 1 else 0 := ok7
    have b7 : (word t7.mem B sBb).toNat = if X = 0 then 1 else 0 := sB7
    rw [or_bits (by rw [o7]; split <;> decide) (by rw [b7]; split <;> decide), o7, b7]
    by_cases hX0 : X = 0
    · simp only [hX0, ↓reduceIte, or_true, isqrt_zero, Nat.mul_zero]
    · obtain ⟨Sv, R, _, eR, hR, hSR⟩ := dv_last (by omega) (hDVk hX0)
      have D6 : num t6.mem B (W2 w) wDig = 0 := by
        rw [f6.num (by decide) (by simp) fD, f5.num (by decide) (by simp) fD, f4.num (by decide) (by decide) fD]
        exact zD3
      have R6 : num t6.mem B (W2 w) wR = R := eR
      have sq := (sqrt_vals hSR hR).2
      rw [D6, R6]
      by_cases hR0 : R = 0
      · simp [hR0, hX0, sq.mp hR0]
      · have nsq : ¬ isqrt X * isqrt X = X := fun e => hR0 (sq.mpr e)
        simp [hR0, hX0, nsq]

end VG.Proof.Rsa.RISCV64.Keys
