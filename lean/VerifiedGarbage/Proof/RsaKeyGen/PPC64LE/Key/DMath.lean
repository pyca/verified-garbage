module

public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
import VerifiedGarbage.Proof.RsaKeyGen.KeyInv
import VerifiedGarbage.Proof.RsaKeyGen.OddInverseQuotient
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on PPC64LE: `d = e⁻¹ mod L` by its three cases

The code computes all three cases of `e` and selects one (`okv`, whether
`d` exists, and `d`):

* `e` odd and at least 3 (with the modulus `mE`, `e`, or 3 otherwise):
  `L = mE Q + R`, `x = R⁻¹ mod mE`, `d = Q (mE - x) + (R (mE - x) + 1) / mE`
  (`Proof/RsaKeyGen/OddInverseQuotient.lean`);
* `e = 1`: `d = 1`, for `L ≠ 1`;
* `e` even (with the modulus `mL`, `L` if it is odd and at least 3, or 3
  otherwise): `d = e⁻¹ mod mL`.

`okv_none`: without `okv`, `Rsa.inverse e L` is `none`; `inverse_odd'`,
`inverse_one'` and `inverse_even'`: with it, the case's `d`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Key

open VG.Proof.RsaKeyGen

/-- The modulus of the odd case: `e`, if it is odd and at least 3, or 3. -/
def mE (e : Nat) : Nat := if ¬ e < 3 ∧ e % 2 = 1 then e else 3

/-- Whether `L` is odd and at least 3. -/
def good (L : Nat) : Prop := ¬ L < 3 ∧ L % 2 = 1

instance (L : Nat) : Decidable (good L) := by unfold good; infer_instance

/-- The modulus of the even case: `L`, if it is odd and at least 3, or 3. -/
def mL (L : Nat) : Nat := if good L then L else 3

/-- Whether `d` exists, by `e`'s case. -/
def okv (e L : Nat) : Prop :=
  (e % 2 = 1 ∧ ((e = 1 ∧ L ≠ 1) ∨ (e ≠ 1 ∧ ¬ L < 2 ∧ Nat.gcd (L % mE e) (mE e) = 1))) ∨
    (e % 2 ≠ 1 ∧ good L ∧ Nat.gcd e (mL L) = 1)

instance (e L : Nat) : Decidable (okv e L) := by unfold okv; infer_instance

theorem mE_odd (e : Nat) : mE e % 2 = 1 ∧ 1 < mE e := by
  unfold mE
  split
  · rename_i h
    have := h.1
    exact ⟨h.2, by omega⟩
  · decide

theorem mL_odd (L : Nat) : mL L % 2 = 1 ∧ 1 < mL L := by
  unfold mL
  by_cases h : good L
  · simp only [h, ↓reduceIte]; unfold good at h; exact ⟨h.2, by omega⟩
  · simp only [h, ↓reduceIte]; decide

theorem mE_of {e : Nat} (h1 : e % 2 = 1) (h2 : e ≠ 1) : mE e = e := by
  unfold mE; simp [show ¬ e < 3 by omega, h1]

theorem mL_of {L : Nat} (h : good L) : mL L = L := by unfold mL; simp [h]

/-- Without `okv`, no inverse. -/
theorem okv_none {e L : Nat} (h : ¬ okv e L) : Spec.Rsa.inverse e L = none := by
  unfold okv at h
  by_cases he : e % 2 = 1
  · by_cases h1 : e = 1
    · have : L = 1 := Decidable.byContradiction fun hL => h (.inl ⟨he, .inl ⟨h1, hL⟩⟩)
      subst h1 this
      exact inverse_mod_one 1
    · rw [mE_of he h1] at h
      exact inverse_odd_none (Q := L / e) (R := L % e) (by omega) (Nat.div_add_mod L e).symm
        fun ⟨a, b⟩ => h (.inl ⟨he, .inr ⟨h1, by omega, b⟩⟩)
  · refine inverse_even_none' (by omega) fun ⟨a, b, c⟩ => h (.inr ⟨he, ⟨by omega, a⟩, ?_⟩)
    rw [mL_of ⟨by omega, a⟩]; exact c

/-- `e` odd, not 1: `d = Q t + (R t + 1) / e`. -/
theorem inverse_odd' {e L x : Nat} (h1 : e % 2 = 1) (h2 : e ≠ 1) (hL : ¬ L < 2)
    (hx : (e : Int) ∣ (x : Int) * (L % e : Nat) - 1) (hxe : x < e) :
    Spec.Rsa.inverse e L = some (L / e * (e - x) + (L % e * (e - x) + 1) / e) :=
  oddQuotient_inverse (Q := L / e) (R := L % e) (by omega) (by omega) (Nat.div_add_mod L e).symm hx hxe

/-- `e = 1`: `d = 1`, for `L ≠ 1`. -/
theorem inverse_one' {L : Nat} (h : L ≠ 1) : Spec.Rsa.inverse 1 L = some 1 := by
  rw [inverse_one]; simp [h]

/-- `e` even: `d = e⁻¹ mod L`, for an odd `L ≥ 3`. -/
theorem inverse_even' {e L x : Nat} (hL : good L) (hx : (L : Int) ∣ (x : Int) * e - 1) (hxL : x < L) :
    Spec.Rsa.inverse e L = some x :=
  VG.Proof.Rsa.inverse_eq (by unfold good at hL; omega) hxL hx

/-- The odd case's numbers fit: `Q t ≤ L` and `R t + 1 < 2^128`, and the
sum `Q t + c ≤ L`, for `t ≤ e < 2^64`. -/
theorem odd_fits {e L x : Nat} (he : e < 2 ^ 64) (h2 : 2 ≤ e) :
    L / e * (e - x) ≤ L ∧ L % e * (e - x) + 1 < 2 ^ 128 ∧
      L / e * (e - x) + (L % e * (e - x) + 1) / e ≤ L := by
  have q : L / e * (e - x) ≤ L / e * e := Nat.mul_le_mul_left _ (Nat.sub_le e x)
  have q' : L / e * e ≤ L := Nat.div_mul_le_self L e
  refine ⟨by omega, odd_numerator_fits he (Nat.mod_lt _ (by omega)), ?_⟩
  exact oddQuotient_le (Q := L / e) (R := L % e) (x := x) (by omega) (Nat.div_add_mod L e).symm

end VG.Proof.RsaKeyGen.PPC64LE.Key
