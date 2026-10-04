import VerifiedGarbage.Proof.Poly1305.Horner
import VerifiedGarbage.Proof.Poly1305.Limbs26

/-!
# Poly1305: Horner's rule in two lanes of two blocks

The arithmetic of AArch64's AdvSIMD `update` (`Impl/Poly1305/AArch64/Vector.lean`),
as Nat identities. Two lanes `A` and `B` absorb a group of four blocks
`m₀ … m₃` as `A ← (A + m₀) r⁴ + m₂ r²` and `B ← (B + m₁) r⁴ + m₃ r²`, which
keeps `A r + B ≡ r a` for the accumulator `a` of the blocks so far (starting
with `A = a`, `B = 0`); the last group multiplies `B + m₁` by `r³` and `m₃` by
`r`, after which `A + B ≡ a`.

The products of five 26-bit limbs, `d_k = Σ_{i ≤ k} x_i y_(k-i) + Σ_{i > k}
x_i (5 y)_(k+5-i)`, are `Limbs26.pd`'s; they are carried in two interleaved
chains (`carry`), and the limbs of the sum of the lanes are put back into
three 64-bit words (`pack`) whose third is then reduced (`fold6`).
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305 (P leNum)
open Limbs26 (val P_eq)

/-! ## Horner's rule in two lanes -/

section
variable {r X A B A' B' : Nat} {b0 b1 b2 b3 : List Byte}
  (h0 : b0.length = 16) (h1 : b1.length = 16) (h2 : b2.length = 16) (h3 : b3.length = 16)
  (hS : A * r + B ≡ r * X [MOD P])
include h0 h1 h2 h3 hS

/-- A group of four blocks. -/
theorem pair_step (eA : A' ≡ (A + mv b0) * r ^ 4 + mv b2 * r ^ 2 [MOD P])
    (eB : B' ≡ (B + mv b1) * r ^ 4 + mv b3 * r ^ 2 [MOD P]) :
    A' * r + B' ≡ r * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := (absorbAll_four (r := r) (a := X) h0 h1 h2 h3).mul_left r
  calc A' * r + B'
      _ ≡ ((A + mv b0) * r ^ 4 + mv b2 * r ^ 2) * r + ((B + mv b1) * r ^ 4 + mv b3 * r ^ 2) [MOD P] :=
        (eA.mul_right r).add eB
      _ = r ^ 4 * (A * r + B) + r * (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) := by
        ring
      _ ≡ r ^ 4 * (r * X) + r * (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) [MOD P] :=
        (hS.mul_left _).add_right _
      _ = r * (r ^ 4 * X + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) := by ring
      _ ≡ r * absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

/-- The last group: then `A' + B'` is the accumulator. -/
theorem pair_last (eA : A' ≡ (A + mv b0) * r ^ 4 + mv b2 * r ^ 2 [MOD P])
    (eB : B' ≡ (B + mv b1) * r ^ 3 + mv b3 * r [MOD P]) :
    A' + B' ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := by
  have hA := absorbAll_four (r := r) (a := X) h0 h1 h2 h3
  calc A' + B'
      _ ≡ ((A + mv b0) * r ^ 4 + mv b2 * r ^ 2) + ((B + mv b1) * r ^ 3 + mv b3 * r) [MOD P] := eA.add eB
      _ = r ^ 3 * (A * r + B) + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) := by ring
      _ ≡ r ^ 3 * (r * X) + (r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3) [MOD P] :=
        (hS.mul_left _).add_right _
      _ = r ^ 4 * X + r ^ 4 * mv b0 + r ^ 3 * mv b1 + r ^ 2 * mv b2 + r * mv b3 := by ring
      _ ≡ absorbAll r X (b0 ++ b1 ++ b2 ++ b3) [MOD P] := hA.symm

end

/-- The lanes start as the accumulator and 0. -/
theorem pair_init (r X : Nat) : X * r + 0 ≡ r * X [MOD P] := by
  rw [Nat.add_zero, Nat.mul_comm]

/-- Absorbing from congruent accumulators gives congruent results. -/
theorem absorbAll_congr {r a a' : Nat} (h : a ≡ a' [MOD P]) (msg : List Byte) :
    absorbAll r a msg ≡ absorbAll r a' msg [MOD P] := by
  unfold absorbAll
  generalize List.range (Spec.Poly1305.numBlocks msg) = l
  cases l with
  | nil => exact h
  | cons i l =>
    simp only [List.foldl_cons]
    rw [show r * (a + leNum (Spec.Poly1305.block msg i ++ [0x01])) % P =
      r * (a' + leNum (Spec.Poly1305.block msg i ++ [0x01])) % P from (h.add_right _).mul_left r]

namespace Pair

/-! ## Products -/

/-- The multiplier of limb `i` of the operand in `d_k`: `y` or `5 y`. -/
def mulL (y : Nat → Nat) (i k : Nat) : Nat := if i ≤ k then y (k - i) else 5 * y (k + 5 - i)

/-- `d_k`, summed in the order of the limbs of the operand. -/
def prod (x y : Nat → Nat) (k : Nat) : Nat :=
  x 0 * mulL y 0 k + x 1 * mulL y 1 k + x 2 * mulL y 2 k + x 3 * mulL y 3 k + x 4 * mulL y 4 k

theorem prod_val (x y : Nat → Nat) : val (prod x y) + P * Limbs26.pc x y = val x * val y := by
  simp only [val, prod, mulL, Limbs26.pc, P_eq, Nat.reduceLeDiff, ite_true, ite_false, Nat.reduceSub,
    Nat.reduceAdd, Nat.le_refl, Nat.zero_le]
  ring

theorem prod_mod (x y : Nat → Nat) : val (prod x y) ≡ val x * val y [MOD P] := by
  have h := prod_val x y
  calc val (prod x y) ≡ val (prod x y) + P * Limbs26.pc x y [MOD P] :=
        (Nat.add_mul_mod_self_left _ _ _).symm
    _ = val x * val y := h

/-! ## Carrying -/

section
variable (d : Nat → Nat)

/-- The two chains, `d₀ → d₁ → d₂ → d₃` and `d₃ → d₄ → d₀ → d₁`, as the code
interleaves them. -/
def d1a : Nat := d 1 + d 0 / 2 ^ 26
def d4a : Nat := d 4 + d 3 / 2 ^ 26
def d2a : Nat := d 2 + d1a d / 2 ^ 26
def h0b : Nat := d 0 % 2 ^ 26 + d4a d / 2 ^ 26 + d4a d / 2 ^ 26 * 2 ^ 2
def h3b : Nat := d 3 % 2 ^ 26 + d2a d / 2 ^ 26

/-- The limbs after carrying. -/
def carry : Nat → Nat
  | 0 => h0b d % 2 ^ 26
  | 1 => d1a d % 2 ^ 26 + h0b d / 2 ^ 26
  | 2 => d2a d % 2 ^ 26
  | 3 => h3b d % 2 ^ 26
  | _ => d4a d % 2 ^ 26 + h3b d / 2 ^ 26

end

theorem carry_val (d : Nat → Nat) : val (carry d) + P * (d4a d / 2 ^ 26) = val d := by
  simp only [val, carry, h0b, h3b, d2a, d1a, d4a, P_eq]
  omega

theorem carry_mod (d : Nat → Nat) : val (carry d) ≡ val d [MOD P] := by
  have h := carry_val d
  calc val (carry d) ≡ val (carry d) + P * (d4a d / 2 ^ 26) [MOD P] :=
        (Nat.add_mul_mod_self_left _ _ _).symm
    _ = val d := h

theorem carry_congr {d d' : Nat → Nat} (h : ∀ k < 5, d k = d' k) (i : Nat) : carry d i = carry d' i := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  rcases i with _ | _ | _ | _ | _ <;> simp only [carry, h0b, h3b, d2a, d1a, d4a, h0, h1, h2, h3, h4]

/-- Products below `2⁶²` carry into limbs below `2²⁷`. -/
theorem carry_lt {d : Nat → Nat} (h : ∀ k < 5, d k < 2 ^ 62) : ∀ i < 5, carry d i < 2 ^ 27 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide)
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [carry, h0b, h3b, d2a, d1a, d4a] <;> omega

/-! ## Bounds of the products -/

/-- Operands below `2²⁸` and multipliers below `2²⁷` (so `5 y` below
`2³⁰`): each `d_k` is below `2⁶⁰`, and a sum of two below `2⁶¹`. -/
theorem prod_lt {x y : Nat → Nat} (hx : ∀ i < 5, x i < 2 ^ 28) (hy : ∀ i < 5, y i < 2 ^ 27) :
    ∀ k < 5, prod x y k < 2 ^ 60 := by
  have hm : ∀ i < 5, ∀ k < 5, mulL y i k < 5 * 2 ^ 27 := by
    intro i hi k hk
    simp only [mulL]
    split
    · have := hy (k - i) (by omega); omega
    · have := hy (k + 5 - i) (by omega); omega
  intro k hk
  have t : ∀ i < 5, x i * mulL y i k < 2 ^ 28 * (5 * 2 ^ 27) := fun i hi =>
    Nat.mul_lt_mul'' (hx i hi) (hm i hi k hk)
  have := t 0 (by decide); have := t 1 (by decide); have := t 2 (by decide)
  have := t 3 (by decide); have := t 4 (by decide)
  simp only [prod]
  omega

end Pair

end VG.Proof.Poly1305
