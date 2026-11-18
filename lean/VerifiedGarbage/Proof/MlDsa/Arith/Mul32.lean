module
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.MlDsa

import VerifiedGarbage.Proof.MlDsa.Arith.Zq
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA: products modulo `q` with 32-bit multiplications, for every target

A target whose only multiplications keep the low 32 bits of the product
(32-bit ARM, see `TCB/Arm/Isa.lean`) cannot form the product of two reduced
values, which has up to 46 bits. It subtracts from the product's low 32 bits
those of a multiple `Q · q` of `q` at most the product and close to it, which
leaves `b · z - Q · q` where that is less than `2³²`:

* `red23 x = x - ⌊x / 2²³⌋ · q` is congruent to `x` and, for `x < 2³²`, at
  most `redMax = 2²³ - 1 + 511 · 8191` (`red23_le`), as `2²³ - q = 8191`;
* `quotN z = ⌊(z + ⌊z / 2¹⁰⌋) / 2⁷⌋` is `2¹⁶ z / q` rounded down, or one
  less, as `2²³ / q = 1 + 2⁻¹⁰ + …`: `2¹⁷ · quotN z ≤ 1025 z`, and
  `1025 q ≤ 2³³`;
* `mulqN b z = b · z - Q · q` for `Q = ⌊⌊b / 2⁸⌋ · quotN z / 2⁸⌋`: for
  `b ≤ redMax` and `z < q`, `⌊b / 2⁸⌋ · quotN z < 2³²`, `Q · q ≤ b · z`, and
  `mulqN b z < 2³² - q` (`mulqN_bounds`), so it is congruent to `b · z`
  (`mulqN_mod`);
* `mulzN b z = red23 (mulqN (red23 b) z)` is congruent to `b · z`
  (`mulzN_mod`) and at most `redMax`, less than `2q`, for any `b < 2³²`.

A target that also has the high word of a 64-bit product (32-bit ARM's
`umaal`) takes the quotient from it: with `zsN z = ⌊2³² z / q⌋`,
`Q = ⌊b (zsN z + 1) / 2³²⌋` is `⌊b z / q⌋` or one more for any `b < 2³²`
and `z < q`, so `mulzUN b z = b · z + q - Q · q` is congruent to `b · z` and
less than `2q` (`mulzUN_bounds`, `mulzUN_mod`); and `z` is the high word of
`zsN z · q + 2³² - 1` (`zsN_zeta`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arith

open VG.Spec.MlDsa

/-- `x - ⌊x / 2²³⌋ · q`. -/
def red23 (x : Nat) : Nat := x - x / 2 ^ 23 * q

/-- The largest value of `red23` on 32 bits. -/
def redMax : Nat := 12574208

theorem red23_le {x : Nat} (hx : x < 2 ^ 32) : red23 x ≤ redMax := by
  unfold red23 redMax; rw [q_eq]; omega_using [hx]

theorem red23_mod (x : Nat) : red23 x % q = x % q := by
  unfold red23
  rw [Nat.mul_comm]
  exact Nat.sub_mul_mod (by rw [q_eq]; omega_using [])

theorem redMax_lt : redMax < 2 * q := by decide

/-- `⌊(z + ⌊z / 2¹⁰⌋) / 2⁷⌋`: `2¹⁶ z / q` rounded down, or one less. -/
def quotN (z : Nat) : Nat := (z + z / 1024) / 128

/-- `b · z - ⌊⌊b / 2⁸⌋ · quotN z / 2⁸⌋ · q`. -/
def mulqN (b z : Nat) : Nat := b * z - b / 256 * quotN z / 256 * q

theorem quotN_lt {z : Nat} (hz : z < q) : quotN z < 65536 := by
  unfold quotN; rw [q_eq] at hz; omega_using [hz]

/-- The product of `mulqN` fits in 32 bits, the multiple of `q` it subtracts
is at most `b · z`, and what is left is less than `2³² - q`. -/
theorem mulqN_bounds {b z : Nat} (hb : b ≤ redMax) (hz : z < q) :
    b / 256 * quotN z < 2 ^ 32 ∧ b / 256 * quotN z / 256 * q ≤ b * z ∧ mulqN b z + q < 2 ^ 32 := by
  unfold redMax at hb
  have hZ := quotN_lt hz
  unfold mulqN
  rw [q_eq] at hz ⊢
  -- `2¹⁷ Z ≤ 1025 z < 2¹⁷ (Z + 1)`
  obtain ⟨z1, z2⟩ : 131072 * quotN z ≤ 1025 * z ∧ 1025 * z < 131072 * quotN z + 131072 := by
    unfold quotN; omega_using []
  generalize quotN z = Z at *
  have pB : b / 256 * Z ≤ 49118 * 65535 := Nat.mul_le_mul (by omega_using [hb]) (by omega_using [hZ])
  -- the products, as atoms
  have a1 : 256 * (b / 256 * Z) ≤ b * Z := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right Z (Nat.mul_div_le b 256)
  have a2 : b * Z ≤ 256 * (b / 256 * Z) + 255 * Z := by
    have : b ≤ 256 * (b / 256) + 255 := by omega_using []
    calc b * Z ≤ (256 * (b / 256) + 255) * Z := Nat.mul_le_mul_right Z this
      _ = 256 * (b / 256 * Z) + 255 * Z := by rw [Nat.add_mul, Nat.mul_assoc]
  have a3 : 131072 * (b * Z) ≤ 1025 * (b * z) := by
    rw [Nat.mul_left_comm, Nat.mul_left_comm 1025]; exact Nat.mul_le_mul_left b z1
  have a4 : 1025 * (b * z) ≤ 131072 * (b * Z) + 131072 * b := by
    rw [Nat.mul_left_comm, Nat.mul_left_comm 131072 b Z, Nat.mul_comm 131072 b, ← Nat.mul_add]
    exact Nat.mul_le_mul_left b (by omega_using [z2])
  have a5 : b * z ≤ 12574208 * 8380416 := Nat.mul_le_mul hb (by omega_using [hz])
  generalize b / 256 * Z = P at *
  generalize b * Z = BZ at *
  generalize b * z = X at *
  refine ⟨by omega_using [pB], by omega_using [a1, a3], ?_⟩
  omega_using [a1, a2, a3, a4, a5, hb, hZ]

theorem mulqN_mod {b z : Nat} (hb : b ≤ redMax) (hz : z < q) : mulqN b z % q = b * z % q := by
  unfold mulqN
  rw [Nat.mul_comm (b / 256 * quotN z / 256)]
  exact Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact (mulqN_bounds hb hz).2.1)

/-- `b · z` modulo `q`, at most `redMax`: `mulqN` of `b` reduced, reduced. -/
def mulzN (b z : Nat) : Nat := red23 (mulqN (red23 b) z)

theorem mulzN_le {b z : Nat} (hb : b < 2 ^ 32) (hz : z < q) : mulzN b z ≤ redMax :=
  red23_le (by have := (mulqN_bounds (red23_le hb) hz).2.2; omega_using [this])

theorem mulzN_mod {b z : Nat} (hb : b < 2 ^ 32) (hz : z < q) : mulzN b z % q = b * z % q := by
  unfold mulzN
  rw [red23_mod, mulqN_mod (red23_le hb) hz, Nat.mul_mod, red23_mod, ← Nat.mul_mod]

/-! ## With the high word of a 64-bit product -/

/-- `⌊2³² z / q⌋`. -/
def zsN (z : Nat) : Nat := 2 ^ 32 * z / q

theorem zsN_lt {z : Nat} (hz : z < q) : zsN z < 2 ^ 32 := by
  unfold zsN
  rw [q_eq] at *
  omega_using [hz]

/-- `z` from `zsN z`: `⌈zsN z · q / 2³²⌉`. -/
theorem zsN_zeta {z : Nat} (hz : z < q) : (zsN z * q + (2 ^ 32 - 1)) / 2 ^ 32 = z := by
  unfold zsN
  rw [q_eq] at *
  omega_using [hz]

/-- `b · z + q - Q · q`, for `Q` the high word of `b · (zsN z + 1)`. -/
def mulzUN (b z : Nat) : Nat := b * z + q - (b * zsN z + b) / 2 ^ 32 * q

theorem mulzUN_bounds {b z : Nat} (hb : b < 2 ^ 32) :
    (b * zsN z + b) / 2 ^ 32 * q ≤ b * z + q ∧ mulzUN b z < 2 * q := by
  have h1 : zsN z * q ≤ 2 ^ 32 * z := Nat.div_mul_le_self _ _
  have h2 : 2 ^ 32 * z < zsN z * q + q := Nat.lt_div_mul_add (by decide)
  obtain h3 : b * zsN z * q ≤ 2 ^ 32 * (b * z) := by
    have := Nat.mul_le_mul_left b h1
    rwa [← Nat.mul_assoc b (zsN z) q, Nat.mul_left_comm b (2 ^ 32) z] at this
  obtain h4 : 2 ^ 32 * (b * z) ≤ b * zsN z * q + b * q := by
    have := Nat.mul_le_mul_left b (Nat.le_of_lt h2)
    rwa [Nat.mul_left_comm b (2 ^ 32) z, Nat.mul_add, ← Nat.mul_assoc b (zsN z) q] at this
  unfold mulzUN
  rw [q_eq] at *
  generalize b * zsN z = X at h3 h4 ⊢
  generalize b * z = A at h3 h4 ⊢
  omega_using [hb, h3, h4]

theorem mulzUN_mod {b z : Nat} (hb : b < 2 ^ 32) : mulzUN b z % q = b * z % q := by
  unfold mulzUN
  rw [Nat.mul_comm ((b * zsN z + b) / 2 ^ 32), Nat.sub_mul_mod (by rw [Nat.mul_comm]; exact (mulzUN_bounds hb).1),
    Nat.add_mod_right]

end VG.Proof.MlDsa.Arith
