import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Int.ModEq

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

/-- `redc`'s result: `A R^K ≡ y R^(K + 1)` gives `A ≡ y R`, `R` invertible
modulo `X`. -/
theorem redc_cancel {X R A y K : Nat} (hR : Nat.Coprime R X) (h : A * R ^ K % X = y * R ^ (K + 1) % X) :
    A % X = y * R % X := by
  have hK : Nat.Coprime (R ^ K) X := Nat.Coprime.pow_left K hR
  apply Nat.ModEq.cancel_right_of_coprime hK.symm
  show A * R ^ K % X = y * R * R ^ K % X
  rw [h, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (R ^ K) R]

/-- A Montgomery multiplication by 1: `Y' R ≡ Y ≡ c R` gives `Y' ≡ c`. -/
theorem mont_one {X R Y Y' c : Nat} (hR : Nat.Coprime R X) (h : Y' * R % X = Y * 1 % X)
    (hY : Y % X = c * R % X) : Y' % X = c % X :=
  Nat.ModEq.cancel_right_of_coprime hR.symm (by rw [Nat.mul_one] at h; exact h.trans hY)

/-- `h = (m₁ - m₂) qInv mod p` from its Montgomery computation: the
difference `(a + P - b) mod P` of `a ≡ m₁ R` and `b ≡ m₂ R` modulo `P`, and
`h R ≡ (a - b) qInv`. -/
theorem crt_h {P R QI m₁ m₂ a b h : Nat} (hP : 0 < P) (hR : Nat.Coprime R P)
    (ha : a % P = m₁ * R % P) (hb : b % P = m₂ * R % P) (hbP : b < P)
    (hh : h * R % P = (a + P - b) % P * QI % P) (hhP : h < P) :
    ((((m₁ : Int) - m₂) * QI) % (P : Int)).toNat = h := by
  -- `d ≡ m₁ - m₂` over the naturals.
  let d := (m₁ % P + P - m₂ % P) % P
  have hd : d + m₂ ≡ m₁ [MOD P] := by
    have h1 : (d + m₂) % P = (m₁ % P + P - m₂ % P + m₂ % P) % P := by
      show ((m₁ % P + P - m₂ % P) % P + m₂) % P = _
      rw [Nat.add_mod ((m₁ % P + P - m₂ % P) % P), Nat.mod_mod, Nat.add_mod (m₁ % P + P - m₂ % P) (m₂ % P),
        Nat.mod_mod]
    have h2 := Nat.mod_lt m₂ hP
    show (d + m₂) % P = m₁ % P
    rw [h1, show m₁ % P + P - m₂ % P + m₂ % P = m₁ % P + P by omega, Nat.add_mod_right, Nat.mod_mod]
  -- `(a - b) mod P ≡ d R`.
  have hT : (a + P - b) % P ≡ d * R [MOD P] := by
    apply Nat.ModEq.add_right_cancel' (m₂ * R)
    have e1 : (a + P - b) % P + m₂ * R ≡ a [MOD P] := by
      have : (a + P - b) % P + b ≡ a [MOD P] := by
        show ((a + P - b) % P + b) % P = a % P
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show a + P - b + b = a + P by omega, Nat.add_mod_right]
      exact (Nat.ModEq.add_left _ hb.symm).trans this
    have e2 : d * R + m₂ * R ≡ a [MOD P] := by
      rw [← Nat.add_mul]; exact (hd.mul_right R).trans ha.symm
    exact e1.trans e2.symm
  -- `h ≡ d qInv`.
  have hh' : h ≡ d * QI [MOD P] := by
    apply Nat.ModEq.cancel_right_of_coprime hR.symm
    show h * R % P = d * QI * R % P
    rw [hh, Nat.mul_assoc, Nat.mul_comm QI R, ← Nat.mul_assoc]
    exact hT.mul_right QI
  have hhd : h = d * QI % P := by rw [← Nat.mod_eq_of_lt hhP]; exact hh'
  -- Over the integers.
  have hdZ : (d : Int) ≡ (m₁ : Int) - m₂ [ZMOD P] := by
    have := (Int.natCast_modEq_iff.mpr hd).sub_right (m₂ : Int)
    push_cast at this
    rwa [Int.add_sub_cancel] at this
  rw [show ((m₁ : Int) - m₂) * QI % P = (d : Int) * QI % P from (hdZ.symm.mul_right _), hhd]
  norm_cast

end VG.Proof.Bignum
