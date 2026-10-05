import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Weierstrass.Field
import Mathlib.Tactic.LinearCombination

/-!
# Inversion by divsteps: the result in Montgomery form

The inversion ends with `f = ±1`, `x (f a) K ≡ 1` (`K = 2^(5 B)`, or `a = 0`
for `x = 0`) and multiplies `a` by `C_f ≡ f K R³` in Montgomery form, which
leaves `toM acc = toM x ^ (p - 2)` for a prime `p > 2` (`inv_toM`).
-/

namespace VG.Proof.Weierstrass

theorem inv_toM {p R X a Cs acc K : Nat} [Fact p.Prime] (hp2 : 2 < p) (hR : UnitMod p R) (hXp : X < p)
    {f : Int} (h0 : X = 0 → a = 0)
    (hspec : X ≠ 0 → ((X : Int) * (f * a) * K) % p = 1 % p)
    (hCs : X ≠ 0 → (Cs : Int) % p = (f * (K * R ^ 3)) % p) (hmul : acc * R % p = a * Cs % p) :
    toM p R acc = toM p R X ^ (p - 2) := by
  apply toF_injective
  have hρ : (R : ZMod p) * toF (rinv p R) = 1 := by
    have := congrArg toF (mul_rinv hR)
    rwa [toF_mul, toF_ofNat, toF_one] at this
  have e1 : (acc : ZMod p) * R = a * Cs := by
    have := (ZMod.natCast_eq_natCast_iff' (acc * R) (a * Cs) p).mpr hmul
    push_cast at this; exact this
  rw [toM, toM, toF_npow, toF_mul, toF_mul, toF_ofNat, toF_ofNat, pow_sub_two_eq_inv hp2]
  set ρ := toF (rinv p R)
  by_cases hX : X = 0
  · have ha := h0 hX
    subst hX ha
    have hacc : (acc : ZMod p) = 0 := by
      have : (acc : ZMod p) * R * ρ = 0 := by rw [e1]; push_cast; ring
      rwa [mul_assoc, hρ, mul_one] at this
    rw [hacc]; push_cast; simp
  · have e2 : (Cs : ZMod p) = f * (K * R ^ 3) := by
      have := (ZMod.intCast_eq_intCast_iff' (Cs : Int) (f * (K * R ^ 3)) p).mpr (hCs hX)
      push_cast at this; exact this
    have e3 : (X : ZMod p) * (f * a) * K = 1 := by
      have := (ZMod.intCast_eq_intCast_iff' _ _ p).mpr (hspec hX)
      push_cast at this; exact this
    refine (eq_inv_of_mul_eq_one_left ?_)
    linear_combination (-ρ ^ 2 * X * acc + X * f * a * K * (R ^ 2 * ρ ^ 2 + R * ρ + 1)) * hρ +
      ρ ^ 3 * X * e1 + ρ ^ 3 * X * a * e2 + e3

end VG.Proof.Weierstrass
