module

public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega

/-! # Bounds and recombination for four half-word products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

/-- A half-word product plus a half-word carry fits in a machine word. -/
theorem half_product_carry_lt {a b c : Nat}
    (ha : a < 65536) (hb : b < 65536) (hc : c < 65536) :
    a * b + c < 2 ^ 32 := by
  have := Nat.mul_le_mul (show a ≤ 65535 by omega_using [ha]) (show b ≤ 65535 by omega_using [hb])
  omega_using [hc, this]

/-- Bounds for every addition used to assemble the product. -/
theorem wide_bounds {a0 a1 b0 b1 : Nat}
    (ha0 : a0 < 65536) (ha1 : a1 < 65536)
    (hb0 : b0 < 65536) (hb1 : b1 < 65536) :
    let p := a0 * b0
    let t := a1 * b0 + p / 65536
    let u := a0 * b1 + t % 65536
    p < 2 ^ 32 ∧ t < 2 ^ 32 ∧ u < 2 ^ 32 ∧
      a1 * b1 + t / 65536 + u / 65536 < 2 ^ 32 := by
  dsimp only
  have hp := half_product_carry_lt ha0 hb0 (c := 0) (by decide)
  have ht := half_product_carry_lt ha1 hb0 (c := a0 * b0 / 65536) (by omega_using [hp])
  have hu := half_product_carry_lt ha0 hb1 (c := (a1 * b0 + a0 * b0 / 65536) % 65536)
    (Nat.mod_lt _ (by decide))
  have hh := Nat.mul_le_mul (show a1 ≤ 65535 by omega_using [ha1]) (show b1 ≤ 65535 by omega_using [hb1])
  exact ⟨by omega_using [hp], ht, hu, by omega_using [ht, hu, hh]⟩

/-- The carry-split construction is the exact full product, not just its
low word. -/
theorem wide_product (a0 a1 b0 b1 : Nat) :
    let p := a0 * b0
    let t := a1 * b0 + p / 65536
    let u := a0 * b1 + t % 65536
    p % 65536 + (u % 65536) * 65536 +
      (a1 * b1 + t / 65536 + u / 65536) * 2 ^ 32 =
      (a0 + a1 * 65536) * (b0 + b1 * 65536) := by
  dsimp only
  have hp := Nat.mod_add_div (a0 * b0) 65536
  have ht := Nat.mod_add_div (a1 * b0 + a0 * b0 / 65536) 65536
  have hu := Nat.mod_add_div (a0 * b1 + (a1 * b0 + a0 * b0 / 65536) % 65536) 65536
  grind

end VG.Proof.Bignum.Arm
