module

public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Spec.X25519
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! # The inversion modulo `p` on AArch64: the numbers

The rows of a batch as integers (`fterm`, `uterm`), the shift of a row of
`f` and `g` (`shift_rep`), and the reduction of a row of `u` and `v`
(`redV_cong`), as the code computes them. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG.Spec.X25519 VG.Proof.Ed25519.Word64

/-- `|m|`, for a word as a signed number. -/
def absN (m : Word) : Nat := m.toInt.natAbs

/-- `X ^ s` for the mask `s` of `m`'s sign: `X`, or `2²⁵⁶ - 1 - X` if `m < 0`. -/
def flipN (m : Word) (X : Nat) : Nat := if m.msb then 2 ^ 256 - 1 - X else X

/-- `|m|` if `m < 0`. -/
def negN (m : Word) : Nat := if m.msb then absN m else 0

/-- `|m|` if `X ^ s` is negative (as four words in two's complement). -/
def topN (m : Word) (X : Nat) : Nat := if 2 ^ 255 ≤ flipN m X then absN m else 0

/-- Four words as a number in two's complement. -/
def sv (X : Nat) : Int := if X < 2 ^ 255 then X else X - 2 ^ 256

theorem toInt_neg {m : Word} (h : m.msb = true) : m.toInt = -(absN m : Int) := by
  unfold absN
  have e := BitVec.toInt_eq_msb_cond m
  rw [h] at e
  simp only [↓reduceIte] at e
  have := m.isLt
  have := Int.natAbs_eq m.toInt
  omega

theorem toInt_pos {m : Word} (h : m.msb = false) : m.toInt = (absN m : Int) := by
  unfold absN
  have e := BitVec.toInt_eq_msb_cond m
  rw [h] at e
  simp only [Bool.false_eq_true, ↓reduceIte] at e
  have := Int.natAbs_eq m.toInt
  omega

/-- One product of a row of `f` and `g`. -/
theorem fterm (m : Word) {X : Nat} (hX : X < 2 ^ 256) :
    ((absN m * flipN m X + negN m : Nat) : Int) - 2 ^ 256 * (topN m X : Int) = m.toInt * sv X := by
  unfold topN flipN negN sv
  cases hm : m.msb
  · rw [toInt_pos hm]
    by_cases hx : X < 2 ^ 255
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hx, show ¬ 2 ^ 255 ≤ X by omega]
      push_cast; ring
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hx, show 2 ^ 255 ≤ X by omega]
      push_cast; ring
  · rw [toInt_neg hm]
    have e : ((2 ^ 256 - 1 - X : Nat) : Int) = 2 ^ 256 - 1 - (X : Int) := by omega
    by_cases hx : X < 2 ^ 255
    · simp only [↓reduceIte, hx, show 2 ^ 255 ≤ 2 ^ 256 - 1 - X by omega]
      rw [Nat.cast_add, Nat.cast_mul, e]; push_cast; ring
    · simp only [↓reduceIte, hx, show ¬ 2 ^ 255 ≤ 2 ^ 256 - 1 - X by omega]
      rw [Nat.cast_add, Nat.cast_mul, e]; push_cast; ring

/-- One product of a row of `u` and `v`. -/
theorem uterm (m : Word) {A : Nat} (hA : A < 2 ^ 256) :
    ((absN m * flipN m A + negN m : Nat) : Int) - 2 ^ 256 * (negN m : Int) = m.toInt * A := by
  unfold flipN negN
  cases hm : m.msb
  · rw [toInt_pos hm]; simp only [Bool.false_eq_true, ↓reduceIte]; push_cast; ring
  · rw [toInt_neg hm]
    simp only [↓reduceIte]
    have e : ((2 ^ 256 - 1 - A : Nat) : Int) = 2 ^ 256 - 1 - (A : Int) := by omega
    rw [Nat.cast_add, Nat.cast_mul, e]; ring

/-- A row of `f` and `g` shifted: `W ≡ R` (mod `2³²⁰`) for `R = 2⁵⁹ R'` with
`|R'| < 2²⁵⁵` leaves `R'` in four words. -/
theorem shift_rep {W : Nat} {R' : Int}
    (hc : (W : Int) % 2 ^ 320 = (2 ^ 59 * R') % 2 ^ 320) (hR : -2 ^ 255 ≤ R' ∧ R' < 2 ^ 255) :
    sv (W / 2 ^ 59 % 2 ^ 256) = R' ∧ W / 2 ^ 59 % 2 ^ 256 < 2 ^ 256 := by
  refine ⟨?_, Nat.mod_lt _ (by decide)⟩
  unfold sv
  split <;> omega

theorem P_val : (P : Int) = 2 ^ 255 - 19 := by simp [P]

theorem extr_toNat (n m : Word) (lsb : Nat) :
    ((n ++ m).extractLsb' lsb 64).toNat = (n.toNat * 2 ^ 64 + m.toNat) / 2 ^ lsb % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]

/-! ## The reduction of a row of `u` and `v` -/

/-- `q = ⌊W / 2²⁵⁵⌋ - [W < 0]` (a word), for five words `W` (`w4` the top). -/
def redQ (w3 w4 : Word) : Word := (w4 ++ w3).extractLsb' 63 64 - (w4 >>> 63)

/-- What `reduce` leaves: `W - 2²⁵⁵ q + 19 q` modulo `2²⁵⁶`, by the words the code computes:
the low four words with `q` added at bit 255, plus `19 q` as four words (its
high word signed, and the mask of its sign above). -/
def redV (w0 w1 w2 w3 w4 : Word) : Nat :=
  let q := redQ w3 w4
  let sg := (0 : Word) - (q >>> 63)
  (val4 w0 w1 w2 (w3 + (q <<< 63)) + val4 (q * 19) (VG.Proof.Ed25519.AArch64.mulHi q 19 - (sg &&& 19))
    sg sg) % 2 ^ 256

theorem sgn_word (q : Word) :
    ((0 : Word) - (q >>> 63)) = if 2 ^ 63 ≤ q.toNat then BitVec.allOnes 64 else 0 := by
  have h : q >>> 63 = if 2 ^ 63 ≤ q.toNat then 1 else 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := q.isLt
    split
    · rw [show (1 : Word).toNat = 1 from rfl]; omega
    · rw [show (0 : Word).toNat = 0 from rfl]; omega
  rw [h]; split <;> decide

/-- The arithmetic of the reduction, on the words' values. -/
theorem red_arith {w0 w1 w2 w3 w4 E n t w3' lo mh s19 hi sg : Nat} {R : Int}
    (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64) (h2 : w2 < 2 ^ 64) (h3 : w3 < 2 ^ 64) (h4 : w4 < 2 ^ 64)
    (hc : ((w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4 : Nat) : Int) % 2 ^ 320 =
      R % 2 ^ 320) (hR : -2 ^ 317 ≤ R ∧ R < 2 ^ 317)
    (hE : E = (w4 * 2 ^ 64 + w3) / 2 ^ 63 % 2 ^ 64) (hn : n = w4 / 2 ^ 63)
    (ht : t = (2 ^ 64 - n + E) % 2 ^ 64) (hw3 : w3' = (w3 + t * 2 ^ 63 % 2 ^ 64) % 2 ^ 64)
    (hlo : lo = t * 19 % 2 ^ 64) (hmh : mh = t * 19 / 2 ^ 64)
    (hs : (2 ^ 63 ≤ t ∧ s19 = 19 ∧ sg = 2 ^ 64 - 1) ∨ (t < 2 ^ 63 ∧ s19 = 0 ∧ sg = 0))
    (hhi : hi = (2 ^ 64 - s19 + mh) % 2 ^ 64) :
    (((w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3' + (lo + 2 ^ 64 * hi + 2 ^ 128 * sg + 2 ^ 192 * sg))
        % 2 ^ 256 : Nat) : Int) % (2 ^ 255 - 19) = R % (2 ^ 255 - 19) := by
  -- the five words as `a + 2²⁵⁵ T`
  obtain ⟨W, hWd⟩ : ∃ W, W = w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4 := ⟨_, rfl⟩
  rw [← hWd] at hc
  have hWl : W < 2 ^ 320 := by omega_using [hWd, h0, h1, h2, h3, h4]
  have hT : (w4 * 2 ^ 64 + w3) / 2 ^ 63 = W / 2 ^ 255 := by omega_using [hWd, h0, h1, h2, h3]
  have hn' : w4 / 2 ^ 63 = W / 2 ^ 319 := by omega_using [hWd, h0, h1, h2, h3]
  have hlow : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * (w3 % 2 ^ 63) = W % 2 ^ 255 := by
    omega_using [hWd, h0, h1, h2, h3]
  have hb : w3 / 2 ^ 63 = W / 2 ^ 255 % 2 := by omega_using [hWd, h0, h1, h2, h3]
  have hp : lo + 2 ^ 64 * mh = t * 19 := by omega_using [hlo, hmh]
  rw [hT] at hE
  rw [hn'] at hn
  clear hT hn' hlo
  obtain ⟨T, hTd⟩ : ∃ T, T = W / 2 ^ 255 := ⟨_, rfl⟩
  obtain ⟨a, had⟩ : ∃ a, a = W % 2 ^ 255 := ⟨_, rfl⟩
  have hWa : W = a + 2 ^ 255 * T := by omega_using [hTd, had]
  rw [← hTd] at hE hb
  rw [← had] at hlow
  by_cases hneg : R < 0
  · -- `W = R + 2³²⁰`
    have hWR : (W : Int) = R + 2 ^ 320 := by omega_using [hc, hR, hWl, hneg]
    have hn1 : n = 1 := by omega_using [hn, hWR, hR, hWl]
    have hE1 : E = T - 2 ^ 64 := by omega_using [hE, hTd, hWR, hR, hWl]
    have ht1 : t = T - 2 ^ 64 - 1 := by omega_using [ht, hn1, hE1, hTd, hWR, hR, hWl]
    obtain ⟨ht63, rfl, rfl⟩ : 2 ^ 63 ≤ t ∧ s19 = 19 ∧ sg = 2 ^ 64 - 1 := by
      rcases hs with h | h
      · exact h
      · omega_using [h.1, ht1, hTd, hWR, hR, hWl]
    have hw3' : w3' = w3 % 2 ^ 63 + 2 ^ 63 := by omega_using [hw3, ht1, hb, h3, hTd, hWR, hR, hWl]
    have hhi' : hi = 2 ^ 64 + mh - 19 := by omega_using [hhi, hmh, ht]
    have hsum : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3' +
        (lo + 2 ^ 64 * hi + 2 ^ 128 * (2 ^ 64 - 1) + 2 ^ 192 * (2 ^ 64 - 1)) =
        a + 2 ^ 255 + 19 * t - 19 * 2 ^ 64 + 2 ^ 256 := by
      rw [hw3', hhi']; omega_using [hlow, hp]
    rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [had, ht])]
    have hX : ((a + 2 ^ 255 + 19 * t - 19 * 2 ^ 64 : Nat) : Int) =
        R + (2 ^ 255 - 19) * ((2 ^ 65 + 1 : Int) - T) := by
      omega_using [hWa, hWR, ht1, hTd, hWl, hR, hneg, had]
    rw [hX, Int.add_mul_emod_self_left]
  · have hWR : (W : Int) = R := by omega_using [hc, hR, hWl, hneg]
    have hn0 : n = 0 := by omega_using [hn, hWR, hR]
    have ht0 : t = T := by omega_using [ht, hn0, hE, hTd, hWR, hR]
    obtain ⟨ht63, rfl, rfl⟩ : t < 2 ^ 63 ∧ s19 = 0 ∧ sg = 0 := by
      rcases hs with h | h
      · omega_using [h.1, ht0, hTd, hWR, hR]
      · exact h
    have hw3' : w3' = w3 % 2 ^ 63 := by omega_using [hw3, ht0, hb, h3, hTd, hWR, hR]
    have hhi' : hi = mh := by omega_using [hhi, hmh, ht0, hTd, hWR, hR]
    have hsum : w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3' +
        (lo + 2 ^ 64 * hi + 2 ^ 128 * 0 + 2 ^ 192 * 0) = a + 19 * t := by
      rw [hw3', hhi']; omega_using [hlow, hp]
    rw [hsum, Nat.mod_eq_of_lt (by omega_using [had, ht0, hTd, hWR, hR])]
    have hX : ((a + 19 * t : Nat) : Int) = R + (2 ^ 255 - 19) * (-(T : Int)) := by
      omega_using [hWa, hWR, ht0]
    rw [hX, Int.add_mul_emod_self_left]

/-- The reduction is `W` modulo `p`, for `W ≡ R` (mod `2³²⁰`) with `|R| < 2³¹⁷`. -/
theorem redV_cong (w0 w1 w2 w3 w4 : Word) {R : Int}
    (hc : ((val4 w0 w1 w2 w3 + 2 ^ 256 * w4.toNat : Nat) : Int) % 2 ^ 320 = R % 2 ^ 320)
    (hR : -2 ^ 317 ≤ R ∧ R < 2 ^ 317) :
    (redV w0 w1 w2 w3 w4 : Int) % P = R % P := by
  have hq := sgn_word (redQ w3 w4)
  simp only [redV]
  rw [hq]
  have ht : (redQ w3 w4).toNat = (2 ^ 64 - (w4 >>> 63).toNat +
      ((w4 ++ w3).extractLsb' 63 64).toNat) % 2 ^ 64 := by
    rw [redQ, BitVec.toNat_sub]
  rw [extr_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at ht
  have hl := (redQ w3 w4).isLt
  rw [P_val]
  simp only [val4] at hc ⊢
  refine red_arith (mh := (VG.Proof.Ed25519.AArch64.mulHi (redQ w3 w4) 19).toNat)
    (s19 := ((if 2 ^ 63 ≤ (redQ w3 w4).toNat then BitVec.allOnes 64 else 0) &&& (19 : Word)).toNat)
    w0.isLt w1.isLt w2.isLt w3.isLt w4.isLt hc hR rfl rfl ht ?_ ?_ ?_ ?_ ?_
  · rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · rw [BitVec.toNat_mul]; rfl
  · simp only [VG.Proof.Ed25519.AArch64.mulHi, BitVec.toNat_ofNat,
      show (19 : Word).toNat = 19 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  · split
    · exact .inl ⟨by assumption, rfl, rfl⟩
    · exact .inr ⟨by omega, rfl, rfl⟩
  · rw [BitVec.toNat_sub]

end VG.Proof.Ed25519.AArch64.Inv
