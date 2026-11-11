module
-- separate module: the mathematics of every target's precomputation, which does not depend on the target

import VerifiedGarbage.Proof.Bignum.CrtGPow
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.ModArith

/-!
# `R_X² mod X` from `R² mod n`, for a factor `X` of `n`

With `R = 2^(64 w)` for the modulus `n` of `w` words and `R_X = 2^(64 w_X)`
for a factor `X` of `w_X ≤ w` words, `R² mod n ≡ 2^(128 w) (mod X)`.
Reduced by `redc` in `K = ⌈w / w_X⌉` chunks and then by `R_X⁻¹` another
`r2Z` times (Montgomery multiplications by 1), it is `2^(64 e)` for the
`e = r2E w w_X` words left, `1 ≤ e ≤ 2 w_X` (`r2E_spec`, `r2_reduced`).
`r2C` doublings then give `2^(128 w_X)` when `w_X < e`, and otherwise
`2^(64 w_X + w_X)`, which six Montgomery squarings (`2^(64 w_X + t) ↦
2^(64 w_X + 2 t)`, `r2_square`) take to `2^(128 w_X) = R_X² mod X`
(`r2_final`). For factors of half the modulus' words, `e = 2 w_X`: there
are no further reductions, doublings or squarings.

All of these counts depend only on `w` and `w_X`. These facts do not depend
on the target.
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- The words `e₀ = 2 w - K w_X` of `2^(64 e₀)` that `redc` leaves of
`2^(128 w)`, `K = ⌈w / w_X⌉`. -/
def r2E0 (w wx : Nat) : Nat := 2 * w - (w + wx - 1) / wx * wx

/-- The further reductions by `R_X⁻¹`, which bring `e₀` to at most `2 w_X`. -/
def r2Z (w wx : Nat) : Nat := (r2E0 w wx - wx - 1) / wx

/-- The words `e = e₀ - r2Z w_X` left after them. -/
def r2E (w wx : Nat) : Nat := r2E0 w wx - r2Z w wx * wx

/-- The doublings after them: to `2^(64 w_X + w_X)` if `e ≤ w_X` (then six
squarings), else to `2^(128 w_X)`. -/
def r2C (w wx : Nat) : Nat := if r2E w wx ≤ wx then 64 * (wx - r2E w wx) + wx else 64 * (2 * wx - r2E w wx)

/-- `1 ≤ e ≤ 2 w_X`, and `(K + Z) w_X + e = 2 w`. -/
theorem r2E_spec {w wx : Nat} (hwx : 1 ≤ wx) (hw : wx ≤ w) :
    1 ≤ r2E w wx ∧ r2E w wx ≤ 2 * wx ∧ ((w + wx - 1) / wx + r2Z w wx) * wx + r2E w wx = 2 * w := by
  obtain ⟨h1, h2⟩ := kBounds (w := w) hwx
  have hz1 := Nat.div_mul_le_self (r2E0 w wx - wx - 1) wx
  have hz2 := Nat.lt_div_mul_add (a := r2E0 w wx - wx - 1) (show 0 < wx by omega)
  unfold r2E r2Z at *
  unfold r2E0 at *
  rw [Nat.add_mul]
  generalize (w + wx - 1) / wx * wx = a at *
  generalize (2 * w - a - wx - 1) / wx * wx = b at *
  omega

/-- Before reduction `j + 1` of the further ones, `2 w_X < e₀ - (j + 1) w_X`
iff another one follows. -/
theorem r2Z_step {w wx j : Nat} (hwx : 1 ≤ wx) (hj : j < r2Z w wx) :
    2 * wx < r2E0 w wx - (j + 1) * wx ↔ j + 1 < r2Z w wx := by
  have e1 := (Nat.le_div_iff_mul_le (k := wx) (x := j + 1) (y := r2E0 w wx - wx - 1) (by omega)).mp
    (by unfold r2Z at hj; omega)
  have e2 := Nat.le_div_iff_mul_le (k := wx) (x := j + 2) (y := r2E0 w wx - wx - 1) (by omega)
  unfold r2Z
  rw [show j + 2 = j + 1 + 1 by omega, Nat.add_mul (j + 1) 1, Nat.one_mul] at e2
  generalize (j + 1) * wx = a at *
  omega

/-- Some further reduction follows `redc` iff `2 w_X < e₀`. -/
theorem r2Z_pos {w wx : Nat} (hwx : 1 ≤ wx) : 0 < r2Z w wx ↔ 2 * wx < r2E0 w wx := by
  have e := Nat.le_div_iff_mul_le (k := wx) (x := 1) (y := r2E0 w wx - wx - 1) (by omega)
  rw [Nat.one_mul] at e
  unfold r2Z
  omega

/-- A further reduction: `A' R_X ≡ A` and `A R_X^k ≡ x` give
`A' R_X^(k + 1) ≡ x`. -/
theorem r2_step {X A A' wx k x : Nat} (h1 : A' * 2 ^ (64 * wx) % X = A % X)
    (hA : A * 2 ^ (64 * wx * k) % X = x % X) : A' * 2 ^ (64 * wx * (k + 1)) % X = x % X := by
  rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm (2 ^ (64 * wx * k)), ← Nat.mul_assoc, Nat.mul_mod,
    h1, ← Nat.mul_mod, hA]

/-- The value after the reductions: `A R_X^(K + Z) ≡ 2^(128 w)` gives
`A ≡ 2^(64 e)`, modulo an odd `X`. -/
theorem r2_reduced {X A w wx : Nat} (hwx : 1 ≤ wx) (hw : wx ≤ w) (hX : X % 2 = 1)
    (hA : A * 2 ^ (64 * wx * ((w + wx - 1) / wx + r2Z w wx)) % X = 2 ^ (128 * w) % X) :
    A % X = 2 ^ (64 * r2E w wx) % X := by
  obtain ⟨-, -, he⟩ := r2E_spec hwx hw
  refine mont_cancel (coprime_pow2 hX (64 * wx * ((w + wx - 1) / wx + r2Z w wx))) ?_
  rw [hA, ← Nat.pow_add]
  congr 2
  rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mul_comm wx, Nat.add_comm, he]
  omega

/-- A Montgomery squaring of `2^(64 w_X + t)`: `2^(64 w_X + 2 t)`. -/
theorem r2_square {X Y Y' wx t : Nat} (hX : X % 2 = 1) (hY : Y = 2 ^ (64 * wx + t) % X) (hlt : Y' < X)
    (h : Y' * 2 ^ (64 * wx) % X = Y * Y % X) : Y' = 2 ^ (64 * wx + 2 * t) % X := by
  have e : Y * Y % X = 2 ^ (64 * wx + 2 * t) * 2 ^ (64 * wx) % X := by
    rw [hY, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add,
      show 64 * wx + t + (64 * wx + t) = 64 * wx + 2 * t + 64 * wx by omega]
  have := mont_cancel (coprime_pow2 hX (64 * wx)) (h.trans e)
  rwa [Nat.mod_eq_of_lt hlt] at this

/-- After the doublings: `2^(64 e + c)` is `2^(64 w_X + w_X)` if `e ≤ w_X`,
else `2^(128 w_X)`. -/
theorem r2_doubled {w wx : Nat} (hwx : 1 ≤ wx) (hw : wx ≤ w) :
    64 * r2E w wx + r2C w wx = if r2E w wx ≤ wx then 64 * wx + wx else 128 * wx := by
  obtain ⟨-, h2, -⟩ := r2E_spec hwx hw
  unfold r2C
  split <;> omega

/-- At most `128 w_X` doublings, as many as from 1. -/
theorem r2C_le {w wx : Nat} (hwx : 1 ≤ wx) (hw : wx ≤ w) : r2C w wx ≤ 128 * wx := by
  obtain ⟨h1, h2, -⟩ := r2E_spec hwx hw
  unfold r2C
  split <;> omega

/-- `R² mod n ≡ 2^(128 w)` modulo a factor `X` of `n`. -/
theorem r2_of_dvd {N X r w : Nat} (hX : X ∣ N) (hr : r % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N) :
    r % X = 2 ^ (128 * w) % X := by
  rw [← Nat.mod_mod_of_dvd r hX, hr, Nat.mod_mod_of_dvd _ hX, ← Nat.pow_add]
  congr 2
  omega

/-- A factor of an odd number is odd. -/
theorem odd_of_dvd {N X : Nat} (hN : N % 2 = 1) (hX : X ∣ N) : X % 2 = 1 := by
  obtain ⟨k, rfl⟩ := hX
  rcases Nat.mod_two_eq_zero_or_one X with h | h
  · rw [Nat.mul_mod, h, Nat.zero_mul] at hN; exact absurd hN (by decide)
  · exact h

/-- Two chunks folded: `a R ≡ h`, `b R ≡ l` and `c R ≡ b` give
`(c + a) R² ≡ l + h R`. -/
theorem fold_mont {X R a b c l h : Nat} (h1 : a * R % X = h % X) (h2 : b * R % X = l % X)
    (h3 : c * R % X = b % X) : (c + a) % X * R * R % X = (l + h * R) % X := by
  rw [Nat.mul_assoc, Nat.mod_mul_mod]
  apply ModArith.mod_eq_of_dvd_sub
  obtain ⟨k₁, e₁⟩ := ModArith.dvd_sub_of_mod_eq h1
  obtain ⟨k₂, e₂⟩ := ModArith.dvd_sub_of_mod_eq h2
  obtain ⟨k₃, e₃⟩ := ModArith.dvd_sub_of_mod_eq h3
  refine ⟨k₂ + k₃ * R + k₁ * R, ?_⟩
  push_cast at e₁ e₂ e₃ ⊢
  grind

/-- After the fold, `A R^2 ≡ 2^(128 w)` gives `A ≡ 2^(64 · 2 (w - v))`, for
`v ≤ w` and an odd `X`. -/
theorem fold_reduced {X A w v : Nat} (hv : v ≤ w) (hX : X % 2 = 1)
    (hA : A * 2 ^ (64 * v) * 2 ^ (64 * v) % X = 2 ^ (128 * w) % X) :
    A % X = 2 ^ (64 * (2 * (w - v))) % X := by
  refine mont_cancel (coprime_pow2 hX (128 * v)) ?_
  rw [show 2 ^ (128 * v) = 2 ^ (64 * v) * 2 ^ (64 * v) by rw [← Nat.pow_add]; congr 1; omega, ← Nat.mul_assoc,
    hA, ← Nat.pow_add, ← Nat.pow_add]
  congr 2
  omega

/-- The fold's doublings: `2^(64 e + c)` for `e = 2 (w - v)`, as `r2_doubled`. -/
theorem fold_doubled {w v : Nat} (hv : v ≤ w) (hw : w ≤ 2 * v) :
    64 * (2 * (w - v)) + (if 2 * (w - v) ≤ v then 64 * (v - 2 * (w - v)) + v else 64 * (2 * v - 2 * (w - v))) =
      if 2 * (w - v) ≤ v then 64 * v + v else 128 * v := by
  split <;> omega

end VG.Proof.Bignum
