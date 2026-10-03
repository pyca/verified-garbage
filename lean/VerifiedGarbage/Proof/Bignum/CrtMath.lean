import VerifiedGarbage.Proof.Bignum.Math

/-!
# Multiword arithmetic: the mathematics of RSA with the CRT

`redc`'s step (`redc_step`): `A ≡ L R^(-k)` becomes
`(A R⁻¹ + c R⁻¹) mod X ≡ (L + c R^k) R^(-(k + 1))`, each `R⁻¹` a
Montgomery multiplication by 1.
-/

namespace VG.Proof.Bignum

/-- A chunk `c` of `redc`: `A R^k ≡ L` becomes `(A' + T) mod X` with
`(A' + T) R^(k + 1) ≡ L + c R^k`, for `A' R ≡ A` and `T R ≡ c`. -/
theorem redc_step {X R A A' T c L k : Nat} (h1 : A' * R % X = A % X) (h2 : T * R % X = c % X)
    (hA : A * R ^ k % X = L % X) : (A' + T) % X * R ^ (k + 1) % X = (L + c * R ^ k) % X := by
  have e1 : (A' + T) % X * R ^ (k + 1) ≡ (A' * R + T * R) * R ^ k [MOD X] := by
    have := (Nat.mod_modEq (A' + T) X).mul_right (R ^ (k + 1))
    rwa [show (A' + T) * R ^ (k + 1) = (A' * R + T * R) * R ^ k by rw [Nat.pow_succ]; ring] at this
  have e2 : (A' * R + T * R) * R ^ k ≡ (A + c) * R ^ k [MOD X] :=
    (Nat.ModEq.add h1 h2).mul_right _
  have e3 : (A + c) * R ^ k ≡ L + c * R ^ k [MOD X] := by
    rw [Nat.add_mul]; exact Nat.ModEq.add_right _ hA
  exact (e1.trans e2).trans e3

end VG.Proof.Bignum
