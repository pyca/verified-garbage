module

public import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Poly1305

/-!
# Poly1305 in 44-bit limbs

The arithmetic of vector implementations that keep numbers modulo `p` in
three limbs of 44 bits (`x₀ + 2⁴⁴ x₁ + 2⁸⁸ x₂`) and multiply them with 52-bit
multiply-adds (`vpmadd52luq`, `vpmadd52huq`): the low and high sums of the
limbs' products, with the terms past `2¹³⁰` taken from twenty times the
multiplier's limbs; the high sums folded into the low ones; and the carrying.
Each function sums in the order the code does, so that the terms the code
computes are these functions by definition.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Limbs44

open VG.Spec.Poly1305 (P)

/-- The number whose limbs are `a 0`, `a 1` and `a 2` (of any size). -/
def val (a : Nat → Nat) : Nat := a 0 + 2 ^ 44 * a 1 + 2 ^ 88 * a 2

theorem P_eq : P = 1361129467683753853853498429727072845819 := by decide

/-- The 52-bit part of a product that a multiply-add adds: the high half if
`h`, else the low one, of the product of the sources' low 52 bits. -/
def madN (h : Bool) (a b : Nat) : Nat :=
  if h then a % 2 ^ 52 * (b % 2 ^ 52) / 2 ^ 52 else a % 2 ^ 52 * (b % 2 ^ 52) % 2 ^ 52

theorem madN_halves {a b : Nat} (ha : a < 2 ^ 52) (hb : b < 2 ^ 52) :
    madN false a b + 2 ^ 52 * madN true a b = a * b := by
  simp only [madN, Bool.false_eq_true, ite_false, ite_true, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  exact Nat.mod_add_div _ _

/-! ## Products -/

section
variable (a b c : Nat → Nat) (h : Bool)

/-- The halves `h` of the products of limb `j`, summed as the code does:
`a₀ b₀ + a₁ c₂ + a₂ c₁`, `a₀ b₁ + a₁ b₀ + a₂ c₂` and `a₀ b₂ + a₁ b₁ + a₂ b₀`,
with `c = 20 b` standing for the terms past `2¹³⁰` (`2¹³² ≡ 20`). -/
def ps : Nat → Nat
  | 0 => 0 + madN h (a 0) (b 0) + madN h (a 1) (c 2) + madN h (a 2) (c 1)
  | 1 => 0 + madN h (a 0) (b 1) + madN h (a 1) (b 0) + madN h (a 2) (c 2)
  | _ => 0 + madN h (a 0) (b 2) + madN h (a 1) (b 1) + madN h (a 2) (b 0)

/-- The high sums folded into the low ones: `u₀ 2⁸` into `l₁`, `u₁ 2⁸` into
`l₂` and `u₂ 5 · 2¹⁰ = u₂ 2¹² + u₂ 2¹⁰` into `l₀`. -/
def pf : Nat → Nat
  | 0 => ps a b c false 0 + ps a b c true 2 * 2 ^ 12 + ps a b c true 2 * 2 ^ 10
  | 1 => ps a b c false 1 + ps a b c true 0 * 2 ^ 8
  | _ => ps a b c false 2 + ps a b c true 1 * 2 ^ 8

end

theorem pf_val {a b c : Nat → Nat} (ha : ∀ i < 3, a i < 2 ^ 52) (hb : ∀ i < 3, b i < 2 ^ 52)
    (hc : ∀ i < 3, c i < 2 ^ 52) (c1 : c 1 = 20 * b 1) (c2 : c 2 = 20 * b 2) :
    val (pf a b c) + P * (4 * (a 1 * b 2 + a 2 * b 1 + 2 ^ 44 * (a 2 * b 2)) +
      2 ^ 10 * ps a b c true 2) = val a * val b := by
  have m : ∀ i < 3, ∀ j < 3, madN false (a i) (b j) + 2 ^ 52 * madN true (a i) (b j) = a i * b j :=
    fun i hi j hj => madN_halves (ha i hi) (hb j hj)
  have n : ∀ i < 3, ∀ j < 3, madN false (a i) (c j) + 2 ^ 52 * madN true (a i) (c j) = a i * c j :=
    fun i hi j hj => madN_halves (ha i hi) (hc j hj)
  have m00 := m 0 (by decide) 0 (by decide)
  have m01 := m 0 (by decide) 1 (by decide)
  have m02 := m 0 (by decide) 2 (by decide)
  have m10 := m 1 (by decide) 0 (by decide)
  have m11 := m 1 (by decide) 1 (by decide)
  have m20 := m 2 (by decide) 0 (by decide)
  have n12 := n 1 (by decide) 2 (by decide)
  have n21 := n 2 (by decide) 1 (by decide)
  have n22 := n 2 (by decide) 2 (by decide)
  simp only [c1, c2] at n12 n21 n22
  simp only [val, pf, ps, P_eq, c1, c2]
  grind

/-! ## Carrying -/

section
variable (f : Nat → Nat)

/-- The limbs carried from `f₀` up: `e₁ = f₁ + f₀ / 2⁴⁴`, `e₂ = f₂ + e₁ / 2⁴⁴`. -/
def e1 : Nat := f 1 + f 0 / 2 ^ 44
def e2 : Nat := f 2 + e1 f / 2 ^ 44
/-- `e₂`'s carry, times 20 (`c 2⁴ + c 2²`), added to `f₀`'s low bits. -/
def g0 (M : Nat) : Nat := (f 0 &&& M) + e2 f / 2 ^ 44 * 2 ^ 4 + e2 f / 2 ^ 44 * 2 ^ 2

/-- The limbs after carrying, with the mask `M = 2⁴⁴ - 1`. -/
def carry (M : Nat) : Nat → Nat
  | 0 => g0 f M &&& M
  | 1 => (e1 f &&& M) + g0 f M / 2 ^ 44
  | _ => e2 f &&& M

end

theorem and_mask (x : Nat) : x &&& 0xfffffffffff = x % 2 ^ 44 := by
  rw [show (0xfffffffffff : Nat) = 2 ^ 44 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem carry_val (f : Nat → Nat) : val (carry f 0xfffffffffff) + P * (4 * (e2 f / 2 ^ 44)) = val f := by
  simp only [val, carry, g0, e2, e1, and_mask, P_eq]
  omega_arith

/-- The product of `a` and `b`, with `c = 20 b` for limbs 1 and 2, carried. -/
def mul (a b c : Nat → Nat) : Nat → Nat := carry (pf a b c) 0xfffffffffff

theorem mul_mod {a b c : Nat → Nat} (ha : ∀ i < 3, a i < 2 ^ 52) (hb : ∀ i < 3, b i < 2 ^ 52)
    (hc : ∀ i < 3, c i < 2 ^ 52) (c1 : c 1 = 20 * b 1) (c2 : c 2 = 20 * b 2) :
    val (mul a b c) % P = val a * val b % P := by
  have h₁ := carry_val (pf a b c)
  have h₂ := pf_val ha hb hc c1 c2
  rw [← h₂, ← h₁, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left, mul]

/-! ## Splitting words into limbs

The limbs of `lo + 2⁶⁴ hi + 2¹²⁸ t` (`lo, hi < 2⁶⁴`), as the code splits
them, are `lo & M`, `(lo >> 44 | hi << 20) & M` and `hi >> 24 | t << 40`
(for a block, `t = 1`, its pad bit). -/

theorem split1 {lo : Nat} (hlo : lo < 2 ^ 64) (hi : Nat) :
    ((lo / 2 ^ 44 ||| hi * 2 ^ 20 % 2 ^ 64) &&& 0xfffffffffff) = lo / 2 ^ 44 + 2 ^ 20 * (hi % 2 ^ 24) := by
  rw [show hi * 2 ^ 20 % 2 ^ 64 = 2 ^ 20 * (hi % 2 ^ 44) by omega_arith, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show lo / 2 ^ 44 < 2 ^ 20 by omega_arith), and_mask]
  omega_arith

theorem split2 {hi : Nat} (hhi : hi < 2 ^ 64) (t : Nat) :
    (hi / 2 ^ 24 ||| t * 2 ^ 40 % 2 ^ 64) = 2 ^ 40 * (t % 2 ^ 24) + hi / 2 ^ 24 := by
  rw [show t * 2 ^ 40 % 2 ^ 64 = 2 ^ 40 * (t % 2 ^ 24) by omega_arith, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show hi / 2 ^ 24 < 2 ^ 40 by omega_arith)]

theorem split_pad {hi : Nat} (hhi : hi < 2 ^ 64) : (hi / 2 ^ 24 ||| 0x10000000000) = 2 ^ 40 + hi / 2 ^ 24 := by
  have := split2 hhi 1
  rwa [show 1 * 2 ^ 40 % 2 ^ 64 = 0x10000000000 by decide, show 1 % 2 ^ 24 = 1 by decide, Nat.mul_one] at this

theorem split_val (lo hi t : Nat) :
    lo % 2 ^ 44 + 2 ^ 44 * (lo / 2 ^ 44 + 2 ^ 20 * (hi % 2 ^ 24)) + 2 ^ 88 * (2 ^ 40 * t + hi / 2 ^ 24) =
      lo + 2 ^ 64 * hi + 2 ^ 128 * t := by
  omega_arith

end VG.Proof.Poly1305.Limbs44
