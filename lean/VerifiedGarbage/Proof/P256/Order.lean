import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.P256.Point
import VerifiedGarbage.Proof.Weierstrass.Order
import VerifiedGarbage.Proof.Weierstrass.Booth

/-!
# P-256: `G` has order `n`

The kernel evaluates the ladder for `n` (`ladRep_n`), whose `Z` is zero, so
`[n]G = O` (`mul_n`); `n` is prime (`Prime.lean`), so the multiples of `G`
below `n` are coprime to it (`n_cop`).
-/

namespace VG.Proof.P256

open Spec.Weierstrass Weierstrass

theorem ladRep_n : (ladRep Spec.P256.curve (Fin.ofNat _ Spec.P256.curve.gx)
    (Fin.ofNat _ Spec.P256.curve.gy) 1 Spec.P256.curve.n 256 256).2.2 = 0 := by
  decide +kernel

theorem mul_n (hC : Law Spec.P256.curve) : mul Spec.P256.curve.n (G Spec.P256.curve) = .infinity :=
  mul_n_of_ladRep hC onCurve_G (by decide +kernel) ladRep_n

theorem n_cop : ∀ m, 0 < m → m < Spec.P256.curve.n → Nat.gcd m Spec.P256.curve.n = 1 := by
  intro m h0 h1
  rcases n_prime.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m Spec.P256.n) with h | h
  · exact h
  · have : Spec.P256.n ∣ m := h ▸ Nat.gcd_dvd_left m Spec.P256.n
    exact absurd (Nat.le_of_dvd h0 this) (by show ¬ (Spec.P256.n ≤ m); exact Nat.not_le.mpr h1)

/-- What the comb with Booth's digits needs of P-256, for its `37` digits of
`7` bits and scalars below `2²⁵⁶`. -/
theorem booth (hC : Law Spec.P256.curve) : BoothOk Spec.P256.curve 7 37 (2 ^ 256) :=
  ⟨mul_n hC, by decide, n_cop, by decide +kernel, by decide, by decide +kernel⟩

end VG.Proof.P256
