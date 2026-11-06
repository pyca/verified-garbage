module
public import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin

import VerifiedGarbage.Proof.Bignum.Math

/-!
# Miller–Rabin in Montgomery form

The implementations keep `y` as `y R mod c` (`R = 2^(64 w)`): a Montgomery
multiplication of `x R mod c` and `z R mod c` is `(x z mod c) R mod c`
(`mont_val`); `y R mod c` is `R mod c` iff `y = 1` and `c − R mod c` iff
`y = c − 1` (`mont_eq_one`, `mont_eq_m1`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

/-- A Montgomery multiplication in canonical form. -/
theorem mont_val {c R O A B x z : Nat} (hR : Nat.Coprime R c) (hO : O < c) (h : O * R % c = A * B % c)
    (hA : A = x * R % c) (hB : B = z * R % c) : O = x * z % c * R % c := by
  rw [← Nat.mod_eq_of_lt hO]
  apply VG.Proof.Bignum.mont_cancel hR
  rw [h, hA, hB, ← Nat.mul_mod, Nat.mul_assoc (x * z % c), Nat.mod_mul_mod]
  congr 1
  simp only [Nat.mul_assoc, Nat.mul_left_comm]

theorem mont_inj {c R x y : Nat} (hR : Nat.Coprime R c) (hx : x < c) (hy : y < c)
    (h : x * R % c = y * R % c) : x = y := by
  have := VG.Proof.Bignum.mont_cancel hR h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem mont_eq_one {c R y : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) (hy : y < c) :
    (y * R % c = R % c) ↔ y = 1 := by
  constructor
  · intro h
    exact mont_inj hR hy hc (by rw [h, Nat.one_mul])
  · rintro rfl; rw [Nat.one_mul]

theorem mont_m1 {c R : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) : (c - 1) * R % c = c - R % c := by
  have hr : 0 < R % c := by
    rcases Nat.eq_zero_or_pos (R % c) with h | h
    · exfalso
      have h1 : Nat.gcd R c = c := Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero h)
      rw [Nat.Coprime] at hR; omega
    · exact h
  have hlt := Nat.mod_lt R (show 0 < c by omega)
  have e : (c - 1) * R + R % c = c * R - (R - R % c) := by
    rw [Nat.sub_mul, Nat.one_mul]
    have := Nat.mod_le R c
    have : R ≤ c * R := Nat.le_mul_of_pos_left R (by omega)
    omega
  have hd : c ∣ R - R % c := Nat.dvd_sub_mod R
  obtain ⟨q, hq⟩ := hd
  have hqR : q ≤ R := by
    have := Nat.sub_le R (R % c)
    rw [hq] at this
    exact Nat.le_trans (Nat.le_mul_of_pos_left q (by omega)) this
  have e2 : (c - 1) * R + R % c = c * (R - q) := by rw [e, hq, Nat.mul_sub]
  have : ((c - 1) * R + R % c) % c = 0 := by rw [e2, Nat.mul_mod_right]
  have h3 : ((c - 1) * R % c + R % c) % c = 0 := by rw [Nat.add_mod, Nat.mod_mod] at this; exact this
  have h4 := Nat.mod_lt ((c - 1) * R) (show 0 < c by omega)
  have h5 : (c - 1) * R % c + R % c = c := by
    rcases Nat.lt_or_ge ((c - 1) * R % c + R % c) c with h | h
    · rw [Nat.mod_eq_of_lt h] at h3; omega
    · have : (c - 1) * R % c + R % c - c < c := by omega
      have e3 := Nat.mod_eq_sub_mod h
      rw [Nat.mod_eq_of_lt this] at e3; omega
  omega

theorem mont_eq_m1 {c R y : Nat} (hR : Nat.Coprime R c) (hc : 1 < c) (hy : y < c) :
    (y * R % c = c - R % c) ↔ y = c - 1 := by
  rw [← mont_m1 hR hc]
  exact ⟨fun h => mont_inj hR hy (by omega) h, fun h => by rw [h]⟩

/-- The bits of an odd `c` and of `c − 1` agree but for bit 0. -/
theorem odd_sub_one_div {c i : Nat} (hc : c % 2 = 1) (hi : 1 ≤ i) : (c - 1) / 2 ^ i = c / 2 ^ i := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    show (c - 1) / 2 = c / 2 by omega]

end VG.Proof.RsaKeyGen
