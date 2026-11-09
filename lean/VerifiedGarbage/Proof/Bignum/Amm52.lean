module

public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Almost Montgomery multiplication in radix `2⁵²`

The arithmetic of AVX512_IFMA's Montgomery multiplication, on natural
numbers: twenty limbs (`L j` for `j < 20`) whose value is
`Σ L j 2^(52 j)` (`lval`), each limb a sum of 52-bit halves of products,
never reduced below `2⁵²` until the end.

A step for the limb `b` of the second operand: the low halves of
`a_j b` into limb `j`; `u = (L₀ k₀) mod 2⁵²` (`stepU`); the low halves of `m_j u`;
the carry of limb 0 into limb 1; the limbs shifted down one; and the high
halves of `a_j b` and `m_j u` into limb `j`. With `m₀ k₀ ≡ -1 (mod 2⁵²)`
the value goes from `V` to `(V + a b + u m) / 2⁵²` exactly,
and twenty steps from 0 give `(a b + Q m) / 2¹⁰⁴⁰` for some `Q < 2¹⁰⁴⁰`
(`steps_alg`), below `2 m` for `a, b < 2 m` and `4 m ≤ 2¹⁰⁴⁰`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Amm52

/-- The low and high 52 bits of the product of the low 52 bits of `x` and `y`. -/
def lo (x y : Nat) : Nat := x % 2 ^ 52 * (y % 2 ^ 52) % 2 ^ 52
def hi (x y : Nat) : Nat := x % 2 ^ 52 * (y % 2 ^ 52) / 2 ^ 52

theorem lo_lt (x y : Nat) : lo x y < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem hi_lt (x y : Nat) : hi x y < 2 ^ 52 := by
  unfold hi
  have hx := Nat.mod_lt x (show 0 < 2 ^ 52 by decide)
  have hy := Nat.mod_lt y (show 0 < 2 ^ 52 by decide)
  refine Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by decide)) ?_)
  exact Nat.le_refl _

theorem lo_hi {x y : Nat} (hx : x < 2 ^ 52) (hy : y < 2 ^ 52) : lo x y + 2 ^ 52 * hi x y = x * y := by
  unfold lo hi
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact Nat.mod_add_div _ _

/-- The value of the limbs below `n`. -/
def lval (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => lval L n + L n * 2 ^ (52 * n)

theorem lval_zero (L : Nat → Nat) : lval L 0 = 0 := rfl
theorem lval_succ (L : Nat → Nat) (n : Nat) : lval L (n + 1) = lval L n + L n * 2 ^ (52 * n) := rfl

-- Unfolding `lval` of 20 limbs computes `2 ^ (52 j)`: keep definitional
-- unfolding out of the proofs (they use `lval_zero` and `lval_succ`).
attribute [irreducible] lval

theorem lval_succ_of {L : Nat → Nat} {n : Nat} (h : L n = 0) : lval L (n + 1) = lval L n := by
  rw [lval_succ, h, Nat.zero_mul, Nat.add_zero]

theorem lval_congr {L L' : Nat → Nat} {n : Nat} (h : ∀ j < n, L j = L' j) : lval L n = lval L' n := by
  induction n with
  | zero => rw [lval_zero, lval_zero]
  | succ n ih => rw [lval_succ, lval_succ, ih fun j hj => h j (by omega), h n (by omega)]

theorem lval_add (L L' : Nat → Nat) (n : Nat) :
    lval (fun j => L j + L' j) n = lval L n + lval L' n := by
  induction n with
  | zero => simp only [lval_zero]
  | succ n ih => rw [lval_succ, lval_succ, lval_succ, ih, Nat.add_mul]; omega

theorem lval_mul (L : Nat → Nat) (c n : Nat) : lval (fun j => L j * c) n = lval L n * c := by
  induction n with
  | zero => simp only [lval_zero, Nat.zero_mul]
  | succ n ih => rw [lval_succ, lval_succ, ih, Nat.add_mul, Nat.mul_right_comm]

/-- Shifted down one limb: `lval L (n + 1) = L 0 + 2⁵² lval (L (· + 1)) n`. -/
theorem lval_succ_shift (L : Nat → Nat) (n : Nat) :
    lval L (n + 1) = L 0 + 2 ^ 52 * lval (fun j => L (j + 1)) n := by
  induction n with
  | zero => simp only [lval_succ, lval_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add]
  | succ n ih =>
    rw [lval_succ, ih, lval_succ, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    grind

theorem lval_lt {L : Nat → Nat} {n : Nat} (h : ∀ j < n, L j < 2 ^ 52) : lval L n < 2 ^ (52 * n) := by
  induction n with
  | zero => rw [lval_zero]; exact Nat.two_pow_pos _
  | succ n ih =>
    have := ih fun j hj => h j (by omega)
    have hn := h n (by omega)
    rw [lval_succ, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    have : L n * 2 ^ (52 * n) ≤ (2 ^ 52 - 1) * 2 ^ (52 * n) := Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ 52 - 1) * 2 ^ (52 * n) + 2 ^ (52 * n) = 2 ^ (52 * n) * 2 ^ 52 := by
      rw [Nat.sub_mul, Nat.one_mul, Nat.mul_comm]
      have : 2 ^ (52 * n) ≤ 2 ^ (52 * n) * 2 ^ 52 := Nat.le_mul_of_pos_right _ (by decide)
      omega
    omega

/-- The operands of a multiplication: the limbs of `a` and of the modulus,
and `k₀ = -m⁻¹ mod 2⁵²`. -/
structure Ops where
  a : Nat → Nat
  m : Nat → Nat
  k0 : Nat

/-- `u` for the limb `b`. -/
def stepU (o : Ops) (L : Nat → Nat) (b : Nat) : Nat := lo (L 0 + lo (o.a 0) b) o.k0

/-- The limbs after the low halves. -/
def low (o : Ops) (L : Nat → Nat) (b : Nat) (j : Nat) : Nat :=
  L j + lo (o.a j) b + lo (o.m j) (stepU o L b)

theorem steps_alg {X V P L0 A M lb lu bn un : Nat} (hX : X = V + A * bn + M * un)
    (h : V * P = L0 + A * lb + M * lu) : X * P = L0 + A * (lb + bn * P) + M * (lu + un * P) := by
  subst hX
  rw [Nat.add_mul, Nat.add_mul, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc]
  omega

/-! ## Twenty steps -/

/-- The bound of an almost Montgomery product: below `2 M` for `A, B < 2 M`
and `4 M ≤ R` (`R = 2¹⁰⁴⁰`). -/
theorem amm_lt {V A B M Q R : Nat} (h : V * R = A * B + M * Q) (hQ : Q < R)
    (hA : A < 2 * M) (hB : B < 2 * M) (hM : 4 * M ≤ R) : V < 2 * M := by
  have h1 : A * B ≤ 4 * M * M := by
    have := Nat.mul_le_mul (Nat.le_of_lt hA) (Nat.le_of_lt hB)
    calc A * B ≤ 2 * M * (2 * M) := this
      _ = 4 * M * M := by grind
  have h2 : 4 * M * M ≤ R * M := Nat.mul_le_mul_right _ hM
  have h3 : M * Q + M ≤ M * R := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hQ
  have : V * R < 2 * M * R := by
    rw [h]
    have e : 2 * M * R = R * M + M * R := by grind
    rw [e]
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · omega
    · omega
  exact Nat.lt_of_mul_lt_mul_right this

/-! ## Carrying -/

/-- The carry into limb `j`, carrying the limbs in order. -/
def carryIn (L : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (L j + carryIn L j) / 2 ^ 52

/-- The limbs carried. -/
def carried (L : Nat → Nat) (j : Nat) : Nat := (L j + carryIn L j) % 2 ^ 52

theorem carried_lt (L : Nat → Nat) (j : Nat) : carried L j < 2 ^ 52 := Nat.mod_lt _ (by decide)

theorem carried_val (L : Nat → Nat) (n : Nat) :
    lval (carried L) n + carryIn L n * 2 ^ (52 * n) = lval L n := by
  induction n with
  | zero => rw [lval_zero, lval_zero, show carryIn L 0 = 0 from rfl]
  | succ n ih =>
    rw [lval_succ, lval_succ, ← ih]
    have e := Nat.div_add_mod (L n + carryIn L n) (2 ^ 52)
    have hc : carryIn L (n + 1) = (L n + carryIn L n) / 2 ^ 52 := rfl
    have hr : carried L n = (L n + carryIn L n) % 2 ^ 52 := rfl
    rw [hc, hr, show 52 * (n + 1) = 52 * n + 52 by omega, Nat.pow_add]
    generalize (L n + carryIn L n) / 2 ^ 52 = q at e ⊢
    generalize (L n + carryIn L n) % 2 ^ 52 = r at e ⊢
    generalize 2 ^ (52 * n) = P
    generalize lval (carried L) n = X
    have : (L n + carryIn L n) * P = (2 ^ 52 * q + r) * P := by rw [e]
    grind

end VG.Proof.Bignum.Amm52
