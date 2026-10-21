module

public import Init.Data.Nat.Gcd

/-! # An even exponent cannot be coprime to an odd candidate minus one -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

theorem even_exponent_rejected {c e : Nat} (odd : c % 2 = 1) (large : 1 < c) (even : e % 2 = 0) :
    Nat.gcd (c - 1) e ≠ 1 := by
  have dc : 2 ∣ c - 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have de : 2 ∣ e := Nat.dvd_of_mod_eq_zero even
  have both := Nat.dvd_gcd dc de
  intro one
  rw [one] at both
  exact (by decide : ¬ 2 ∣ 1) both

end VG.Proof.RsaKeyGen
