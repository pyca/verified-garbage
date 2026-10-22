module

public import VerifiedGarbage.Proof.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.RootPowers

/-! # Square roots from the existing curve-law interface

The group-law interface already supplies the field facts needed for root
recovery. This keeps finite-field algebra in the existing curve variants;
the machine-code proofs require no new trusted facts or variant interface.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- Fermat's identity follows from the existing affine-coordinate law,
applied to a representative of `(1, 1)`. -/
theorem root_fermat (hL : Law C) (hp : 2 < C.p) (y : Fe C) (hy : y ≠ 0) :
    y ^ (C.p - 1) = 1 := by
  have hrep : Rep C y y y (.affine 1 1) := ⟨hy, by grind, by grind⟩
  have h := hL.x_eq hrep
  rw [show C.p - 1 = (C.p - 2) + 1 by omega, Lean.Grind.Semiring.pow_succ]
  grind

theorem root_pow_card (hL : Law C) (hp : 2 < C.p) (y : Fe C) : y ^ C.p = y := by
  by_cases hy : y = 0
  · rw [hy]
    calc
      (0 : Fe C) ^ C.p = (0 : Fe C) ^ ((C.p - 1) + 1) :=
        congrArg (fun n : Nat => (0 : Fe C) ^ n) (by omega)
      _ = 0 := by rw [Lean.Grind.Semiring.pow_succ]; grind
  · calc
      y ^ C.p = y ^ ((C.p - 1) + 1) := congrArg (fun n : Nat => y ^ n) (by omega)
      _ = y := by rw [Lean.Grind.Semiring.pow_succ, root_fermat hL hp y hy,
        Lean.Grind.Semiring.one_mul]

/-- Over the curve's field, two square roots differ only by sign. -/
theorem square_roots_eq_or_neg (hL : Law C) {x y : Fe C} (h : x * x = y * y) :
    x = y ∨ x = -y := by
  by_cases he : x = y
  · exact Or.inl he
  · have hsub : x - y ≠ 0 := by intro h0; apply he; grind
    have hsum : x + y = 0 := by
      by_cases hn : x + y = 0
      · exact hn
      · exact False.elim (hL.mul_ne_zero hsub hn (by grind))
    exact Or.inr (by grind)

theorem sqrt_three_mod_four (hL : Law C) (hp : C.p % 4 = 3) (y : Fe C) :
    ((y * y) ^ ((C.p + 1) / 4)) ^ 2 = y * y := by
  rw [← Lean.Grind.Semiring.pow_two, pow_mul_exponents, pow_mul_exponents,
    show 2 * (((C.p + 1) / 4) * 2) = C.p + 1 by omega,
    Lean.Grind.Semiring.pow_succ, root_pow_card hL (by omega), Lean.Grind.Semiring.pow_two]

theorem sqrt_three_mod_four_iff (hL : Law C) (hp : C.p % 4 = 3) (a : Fe C) :
    (a ^ ((C.p + 1) / 4)) ^ 2 = a ↔ ∃ y : Fe C, y * y = a := by
  constructor
  · intro h
    exact ⟨a ^ ((C.p + 1) / 4), by simpa only [Lean.Grind.Semiring.pow_two] using h⟩
  · rintro ⟨y, rfl⟩
    exact sqrt_three_mod_four hL hp y

theorem rootFacts_three_mod_four (hL : Law C) (hp : C.p % 4 = 3) :
    EcKey.Compressed.RootFacts (Impl.EcKey.Compressed.rootThreeModFour (p := C.p)) := by
  constructor
  · intro a ha
    simp only [Impl.EcKey.Compressed.rootThreeModFour, pow_eq_npow]
    simpa only [Lean.Grind.Semiring.pow_two] using (sqrt_three_mod_four_iff hL hp a).mpr ha
  · exact square_roots_eq_or_neg hL

end VG.Proof.Weierstrass
