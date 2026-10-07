import VerifiedGarbage.Proof.Divstep.Tc32Red

/-! # Finishing a 32-bit divstep reduction with one conditional subtraction -/
namespace VG.Proof.Divstep.W32

theorem norm_first_mod {p r : Int} (_hp : 0 < p) (hr : -p < r ∧ r < 2 * p) :
    (r + if r < 0 then p else 0) % p = norm p r := by
  unfold norm
  by_cases h : r < 0
  · simp only [h, ↓reduceIte]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · simp only [h, ↓reduceIte, Int.add_zero]
    by_cases h' : p ≤ r
    · simp only [h', ↓reduceIte]
      calc
        r % p = ((r - p) + p) % p := by rw [Int.sub_add_cancel]
        _ = (r - p) % p := Int.add_emod_right _ _
        _ = r - p := Int.emod_eq_of_lt (by omega) (by omega)
    · simp only [h', ↓reduceIte]
      exact Int.emod_eq_of_lt (by omega) (by omega)

theorem mred_first_nat {A B H p m W k E R R₁ : Nat} {t : Int}
    (hB : B = 2 ^ 32) (hH : H = 2 ^ 31) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 31 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B)) :
    R₁ < 2 * p ∧ ((R₁ % p : Nat) : Int) = mred p m t := by
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_two_pow
  have hk1 : k < B := by rw [hk]; exact Nat.mod_lt _ (by omega)
  have F : (R₁ : Int) = mredRaw p m t + if mredRaw p m t < 0 then (p : Int) else 0 := by
    refine mred_first_words (A := A) (B := B) (H := H) (p := p) (m := m) (t := t)
      (W := W) (k := k) (E := E) (R := R) (R₁ := R₁)
      (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA)
      (by exact_mod_cast hp) (by exact_mod_cast hpA) (by exact_mod_cast hm) ht
      (by omega) (by exact_mod_cast hW1) (by exact_mod_cast hWt)
      (by omega) (by exact_mod_cast hk1) ?_ ?_ ?_ ?_
    · rw [hk]
      have h1 : W % B * m % B = W * m % B := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
      rw [h1]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
    · rw [hE, ← Nat.cast_mul A H, ite_natCast_le]; push_cast [Nat.cast_sub hB1]; rfl
    · rw [hR]; push_cast; rfl
    · rw [hR₁, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl
  have hm' : ((p : Int) * m + 1) % 2 ^ 32 = 0 := by rw [hB] at hm; exact_mod_cast hm
  have hp' : (0 : Int) < p := by omega
  have bounds := mredRaw_range hp' hm' ht
  constructor
  · split at F <;> omega
  · rw [Int.natCast_emod, F]
    exact norm_first_mod hp' bounds

end VG.Proof.Divstep.W32
