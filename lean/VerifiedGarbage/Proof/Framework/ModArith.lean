module

/-!
# Congruences of naturals, from core Lean alone

Lemmas about `a % n = b % n` that Mathlib states with `Nat.ModEq`, proven
from core's `Nat.gcd` and `Nat.Coprime` lemmas, so that the modules using
them need not import Mathlib's number theory (`Mathlib.Data.Int.ModEq` and
its algebra: hundreds of modules in every importer's closure).
-/

@[expose] public section

namespace VG.ModArith

/-- `a ≡ b (mod n)` from `n ∣ b - a` over the integers. -/
theorem mod_eq_of_dvd_sub {n a b : Nat} (h : (n : Int) ∣ (b : Int) - a) : a % n = b % n := by
  have := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h)
  exact Int.natCast_inj.mp (by rw [Int.natCast_emod, Int.natCast_emod]; exact this.symm)

/-- `n ∣ b - a` over the integers from `a ≡ b (mod n)`. -/
theorem dvd_sub_of_mod_eq {n a b : Nat} (h : a % n = b % n) : (n : Int) ∣ (b : Int) - a := by
  apply Int.dvd_of_emod_eq_zero
  apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
  rw [← Int.natCast_emod, ← Int.natCast_emod, h]

/-- Cancelling a factor coprime to the modulus: `a c ≡ b c (mod n)` gives
`a ≡ b (mod n)`. -/
theorem mod_eq_of_mul_mod_eq {n a b c : Nat} (hc : Nat.Coprime c n) (h : a * c % n = b * c % n) :
    a % n = b % n := by
  have hd : ∀ {x y : Nat}, x * c % n = y * c % n → x % n ≤ y % n → x % n = y % n := by
    intro x y hxy hle
    have e : (y % n - x % n) * c % n = 0 := by
      rw [Nat.sub_mul]
      apply Nat.sub_mod_eq_zero_of_mod_eq
      rw [Nat.mod_mul_mod, Nat.mod_mul_mod, hxy]
    have hdvd : n ∣ y % n - x % n :=
      (Nat.Coprime.dvd_of_dvd_mul_right hc.symm (Nat.dvd_of_mod_eq_zero e))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [Nat.mod_zero] at hle ⊢
      simp only [Nat.mod_zero] at hdvd
      exact (Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp (Nat.eq_zero_of_zero_dvd hdvd))).symm ▸ rfl
    · have := Nat.mod_lt y hn
      have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
  rcases Nat.le_total (a % n) (b % n) with hle | hle
  · exact hd h hle
  · exact (hd h.symm hle).symm

/-- Bézout's identity: `gcd a b = x a + y b` for some integers `x y`. -/
theorem exists_gcd_eq (a b : Nat) : ∃ x y : Int, (Nat.gcd a b : Int) = x * a + y * b := by
  induction a, b using Nat.gcd.induction with
  | H0 n => exact ⟨0, 1, by simp⟩
  | H1 m n _ ih =>
    obtain ⟨x, y, h⟩ := ih
    refine ⟨y - x * (n / m : Nat), x, ?_⟩
    rw [Nat.gcd_rec, h]
    have e : ((n % m : Nat) : Int) = n - m * (n / m : Nat) := by
      have := Nat.mod_add_div n m
      omega
    rw [e]
    grind

/-- With `c` coprime to `n ≠ 0`, every residue is a multiple of `c`:
`u c ≡ a (mod n)` for some `u < n`. -/
theorem exists_mul_mod_eq {n c : Nat} (hc : Nat.Coprime c n) (hn : n ≠ 0) (a : Nat) :
    ∃ u, u < n ∧ u * c % n = a % n := by
  obtain ⟨x, y, h⟩ := exists_gcd_eq c n
  rw [hc] at h
  have hn' : (0 : Int) < n := by omega
  refine ⟨((a * x) % (n : Int)).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos (a * x) hn'
    omega
  · apply mod_eq_of_dvd_sub
    rw [Int.natCast_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn))]
    -- `a - (a x mod n) c = a (x c + y n) - (a x - n (a x / n)) c`
    have hq := Int.mul_ediv_add_emod (a * x) n
    refine ⟨a * y + (a * x / n) * c, ?_⟩
    have : (a : Int) = a * (x * c + y * n) := by rw [← h, Int.natCast_one, Int.mul_one]
    grind

end VG.ModArith
