module

public import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Montgomery multiplication in radix `2³²`, on any target

The arithmetic of finely integrated operand scanning with 32-bit digits in
64-bit registers (`Impl/Bignum/PPC64LE/MontMul.lean`): a digit step adds a
product of digits and two more digits, which fits in 64 bits, and keeps two
carries (`step_eq`); a round divides `T + a b + u m` by `2³²` and keeps it
below `2m` (`round_lt`); the rounds' invariant (`round_step`); the choice of
`u` (`mont_low`).
-/

@[expose] public section

namespace VG.Proof.Bignum.Fios32

/-- A product of two digits plus two digits fits in 64 bits. -/
theorem mac_lt {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    c + a * b + d < 2 ^ 64 := by
  have : a * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have e : (2 ^ 32 - 1) * (2 ^ 32 - 1) = 2 ^ 64 - 2 ^ 33 + 1 := by decide
  omega

/-- The carry of such a sum is a digit. -/
theorem mac_div_lt {a b c d : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32)
    (hd : d < 2 ^ 32) : (c + a * b + d) / 2 ^ 32 < 2 ^ 32 :=
  Nat.div_lt_of_lt_mul (by have := mac_lt ha hb hc hd; omega)

/-- A digit step: `x = t + a b + c₁`, `y = x mod 2³² + u m + c₂`, whose
digit `y mod 2³²` and carries `x / 2³²`, `y / 2³²` make up `t + a b + u m +
c₁ + c₂`. -/
theorem step_eq (t a b u m c₁ c₂ : Nat) :
    t + a * b + u * m + c₁ + c₂ =
      (((t + a * b + c₁) % 2 ^ 32) + u * m + c₂) % 2 ^ 32 +
        2 ^ 32 * ((t + a * b + c₁) / 2 ^ 32 + (((t + a * b + c₁) % 2 ^ 32) + u * m + c₂) / 2 ^ 32) := by
  have h1 := Nat.div_add_mod (t + a * b + c₁) (2 ^ 32)
  have h2 := Nat.div_add_mod (((t + a * b + c₁) % 2 ^ 32) + u * m + c₂) (2 ^ 32)
  rw [Nat.mul_add]
  omega

/-- The sum of a round is below `2³³ m`, if `T < 2m`, `a < 2³²`, `b < m` and
`u < 2³²`. -/
theorem round_sum_lt {T a b u m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32) (hb : b < m)
    (hu : u < 2 ^ 32) : T + a * b + u * m < 2 ^ 32 * (2 * m) := by
  have h1 : a * b ≤ (2 ^ 32 - 1) * b := Nat.mul_le_mul_right _ (by omega)
  have h2 : u * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have h3 : (2 ^ 32 - 1) * b ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.sub_mul, Nat.one_mul] at h1 h2 h3
  have : 2 ^ 32 * (2 * m) = 2 * (2 ^ 32 * m) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ 32) 2, Nat.mul_assoc]
  omega

/-- A round keeps the accumulator below `2m`. -/
theorem round_lt {T T' a b u m : Nat} (h : 2 ^ 32 * T' = T + a * b + u * m) (hT : T < 2 * m)
    (ha : a < 2 ^ 32) (hb : b < m) (hu : u < 2 ^ 32) : T' < 2 * m := by
  have := round_sum_lt hT ha hb hu
  rw [← h] at this
  exact Nat.lt_of_mul_lt_mul_left this

/-- The rounds' invariant `2^(32 i) T ≡ A_i b (mod m)`, one round on. -/
theorem round_step {P T T' a b u m A : Nat} (h : 2 ^ 32 * T' = T + a * b + u * m)
    (hI : P * T % m = A * b % m) : P * 2 ^ 32 * T' % m = (A + P * a) * b % m := by
  have e : P * 2 ^ 32 * T' = P * T + P * a * b + P * u * m := by
    rw [Nat.mul_assoc, h, Nat.mul_add, Nat.mul_add, Nat.mul_assoc P a, Nat.mul_assoc P u]
  rw [e, Nat.add_mul_mod_self_right, Nat.add_mod, hI, ← Nat.add_mod, Nat.add_mul]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`, for the low digits. -/
theorem minv_low {m minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (m % 2 ^ 32 * (minv % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  have h' : (m * minv + 1) % 2 ^ 32 = 0 := by
    have := Nat.mod_mod_of_dvd (m * minv + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩)
    rw [← this, h]
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  exact h'

/-- `x + (x m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low (x m' m : Nat) (h : (m * m' + 1) % 2 ^ 32 = 0) :
    (x + x * m' % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (x * m' % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show x + x * m' * m = x * (m * m' + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm m' m, Nat.add_comm],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- The invariant of a row's pass, one digit on: the low `j + 1` digits of
`T + a b + u m` (`T_L`, `V_b`, `V_m`) are `2³²` times the digits stored
(`S`) plus the carries, at `P = 2^(32 (j + 1))`; with digit `j + 1` (`t`,
`b`, `m`) and the step's digit `y` and carries, the same holds at `2³² P`,
with `y` stored at `Q = 2^(32 j)`. -/
theorem row_step {TL a VB u VM S P Q c₁ c₂ t b m y c₁' c₂' : Nat} (hQ : 2 ^ 32 * Q = P)
    (hI : TL + a * VB + u * VM = 2 ^ 32 * S + P * (c₁ + c₂))
    (hs : t + a * b + u * m + c₁ + c₂ = y + 2 ^ 32 * (c₁' + c₂')) :
    (TL + P * t) + a * (VB + P * b) + u * (VM + P * m) =
      2 ^ 32 * (S + Q * y) + P * 2 ^ 32 * (c₁' + c₂') := by
  grind

/-- The top digit of a round: with the invariant at `P = 2^(32 n)` (`L` the
low `n` digits of `T + a b + u m`, `S` the `n - 1` digits stored), `x = tₙ +
c₁` and `y = x mod 2³² + c₂`, storing `y mod 2³²` at `Q = 2^(32 (n - 1))`
and `x / 2³² + y / 2³²` at `P` makes the stored number `(L + P tₙ) / 2³²`. -/
theorem top_eq {S L P Q tn c₁ c₂ : Nat} (hQ : 2 ^ 32 * Q = P) (hI : L = 2 ^ 32 * S + P * (c₁ + c₂))
    (htn : tn < 2 ^ 32) (hc1 : c₁ < 2 ^ 32) (hc2 : c₂ < 2 ^ 32) :
    2 ^ 32 * (S + Q * (((tn + c₁) % 2 ^ 32 + c₂) % 2 ^ 32) +
      P * (((tn + c₁) / 2 ^ 32 + ((tn + c₁) % 2 ^ 32 + c₂) / 2 ^ 32) % 2 ^ 32)) = L + P * tn := by
  have hx := Nat.div_add_mod (tn + c₁) (2 ^ 32)
  have hy := Nat.div_add_mod ((tn + c₁) % 2 ^ 32 + c₂) (2 ^ 32)
  have hsmall : (tn + c₁) / 2 ^ 32 + ((tn + c₁) % 2 ^ 32 + c₂) / 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hsmall]
  generalize (tn + c₁) / 2 ^ 32 = a at *
  generalize (tn + c₁) % 2 ^ 32 = b at *
  generalize (b + c₂) / 2 ^ 32 = c at *
  generalize (b + c₂) % 2 ^ 32 = d at *
  subst hI hQ
  grind

end VG.Proof.Bignum.Fios32
