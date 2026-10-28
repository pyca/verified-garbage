module

public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.ModArith
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Multiword arithmetic: the mathematics of RSA with the CRT

`redc`'s step (`redc_step`): `A ≡ L R^(-k)` becomes
`(A R⁻¹ + c R⁻¹) mod X ≡ (L + c R^k) R^(-(k + 1))`, each `R⁻¹` a
Montgomery multiplication by 1.
-/

@[expose] public section

namespace VG.Proof.Bignum

/-- A chunk `c` of `redc`: `A R^k ≡ L` becomes `(A' + T) mod X` with
`(A' + T) R^(k + 1) ≡ L + c R^k`, for `A' R ≡ A` and `T R ≡ c`. -/
theorem redc_step {X R A A' T c L k : Nat} (h1 : A' * R % X = A % X) (h2 : T * R % X = c % X)
    (hA : A * R ^ k % X = L % X) : (A' + T) % X * R ^ (k + 1) % X = (L + c * R ^ k) % X := by
  rw [Nat.mod_mul_mod]
  apply ModArith.mod_eq_of_dvd_sub
  obtain ⟨k₁, e₁⟩ := ModArith.dvd_sub_of_mod_eq h1
  obtain ⟨k₂, e₂⟩ := ModArith.dvd_sub_of_mod_eq h2
  obtain ⟨k₃, e₃⟩ := ModArith.dvd_sub_of_mod_eq hA
  refine ⟨k₃ + (k₁ + k₂) * R ^ k, ?_⟩
  push_cast at e₁ e₂ e₃ ⊢
  grind

/-- `redc`'s result: `A R^K ≡ y R^(K + 1)` gives `A ≡ y R`, `R` invertible
modulo `X`. -/
theorem redc_cancel {X R A y K : Nat} (hR : Nat.Coprime R X) (h : A * R ^ K % X = y * R ^ (K + 1) % X) :
    A % X = y * R % X := by
  apply ModArith.mod_eq_of_mul_mod_eq (Nat.Coprime.pow_left K hR)
  rw [h, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (R ^ K) R]

/-- A Montgomery multiplication by 1: `Y' R ≡ Y ≡ c R` gives `Y' ≡ c`. -/
theorem mont_one {X R Y Y' c : Nat} (hR : Nat.Coprime R X) (h : Y' * R % X = Y * 1 % X)
    (hY : Y % X = c * R % X) : Y' % X = c % X :=
  ModArith.mod_eq_of_mul_mod_eq hR (by rw [Nat.mul_one] at h; exact h.trans hY)

/-- `h = (m₁ - m₂) qInv mod p` from its Montgomery computation: the
difference `(a + P - b) mod P` of `a ≡ m₁ R` and `b ≡ m₂ R` modulo `P`, and
`h R ≡ (a - b) qInv`. -/
theorem crt_h {P R QI m₁ m₂ a b h : Nat} (hP : 0 < P) (hR : Nat.Coprime R P)
    (ha : a % P = m₁ * R % P) (hb : b % P = m₂ * R % P) (hbP : b < P)
    (hh : h * R % P = (a + P - b) % P * QI % P) (hhP : h < P) :
    ((((m₁ : Int) - m₂) * QI) % (P : Int)).toNat = h := by
  have hP' : (0 : Int) < P := by omega
  -- `w = z mod P` for `z = (m₁ - m₂) qInv`, as a natural.
  generalize hz : ((m₁ : Int) - m₂) * QI = z
  have hw : (((z % P).toNat : Nat) : Int) = z % P := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hwP : (z % P).toNat < P := by have := Int.emod_lt_of_pos z hP'; omega
  generalize (z % P).toNat = w at hw hwP ⊢
  -- `w R ≡ h R`, each difference below a multiple of `P`.
  have hwh : w * R % P = h * R % P := by
    apply ModArith.mod_eq_of_dvd_sub
    obtain ⟨k₁, e₁⟩ := ModArith.dvd_sub_of_mod_eq ha
    obtain ⟨k₂, e₂⟩ := ModArith.dvd_sub_of_mod_eq hb
    obtain ⟨k₃, e₃⟩ := ModArith.dvd_sub_of_mod_eq hh
    obtain ⟨k₄, e₄⟩ := ModArith.dvd_sub_of_mod_eq (Nat.mod_mod (a + P - b) P)
    have e₅ := Int.mul_ediv_add_emod z P
    have e₆ : ((a + P - b : Nat) : Int) = a + P - b := by omega
    refine ⟨-k₃ - k₄ * QI + (1 - k₁ + k₂) * QI + z / P * R, ?_⟩
    push_cast at e₁ e₂ e₃ e₄ ⊢
    rw [e₆] at e₄
    grind
  have := ModArith.mod_eq_of_mul_mod_eq hR hwh
  rwa [Nat.mod_eq_of_lt hwP, Nat.mod_eq_of_lt hhP] at this

/-- Every residue is in Montgomery form: `a ≡ u R` for some `u`, `R`
invertible modulo `X`. -/
theorem exists_mont {R X : Nat} (hR : Nat.Coprime R X) (hX : X ≠ 0) (a : Nat) : ∃ u, a % X = u * R % X :=
  let ⟨u, _, h⟩ := ModArith.exists_mul_mod_eq hR hX a
  ⟨u, h.symm⟩

end VG.Proof.Bignum
