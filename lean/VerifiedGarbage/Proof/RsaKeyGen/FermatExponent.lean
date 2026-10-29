module

public import Mathlib.Data.Nat.Prime.Defs

/-! # Coprimality for RSA's usual public exponent

65537 is prime, so a candidate minus one is coprime to it exactly when
its whole-word trial reduction is nonzero. This permits the normal exponent
to reuse the native trial kernel; other exponents need the general check.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem prime65537 : Nat.Prime 65537 := by
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

theorem coprime65537 (c : Nat) : Nat.gcd c 65537 = 1 ↔ c % 65537 ≠ 0 := by
  change Nat.Coprime c 65537 ↔ _
  rw [Nat.coprime_comm, prime65537.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]

end VG.Proof.RsaKeyGen
