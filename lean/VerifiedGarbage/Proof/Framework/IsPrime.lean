module

public import Init.Data.Nat.Coprime
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Primality, without Mathlib

`IsPrime`, for the statements of modules that many others import: they need
not load Mathlib to state that a modulus is prime, nor the certificates
(`Framework/Pratt.lean`) to prove it. It is the right side of Mathlib's
`Nat.prime_def`, so a proof that needs Mathlib's algebra takes
`Nat.prime_def.mpr h`.
-/

@[expose] public section

namespace VG.Proof

/-- `p` is prime: at least 2, with no divisors but 1 and `p`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

namespace IsPrime

variable {p : Nat}

theorem two_le (hp : IsPrime p) : 2 ≤ p := hp.1

theorem one_lt (hp : IsPrime p) : 1 < p := hp.1

theorem pos (hp : IsPrime p) : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1

theorem ne_one (hp : IsPrime p) : p ≠ 1 := Nat.ne_of_gt hp.1

theorem eq_one_or_self_of_dvd (hp : IsPrime p) (d : Nat) (h : d ∣ p) : d = 1 ∨ d = p := hp.2 d h

theorem coprime_iff_not_dvd (hp : IsPrime p) {n : Nat} : Nat.Coprime p n ↔ ¬ p ∣ n := by
  constructor
  · intro h hd
    rw [Nat.Coprime, Nat.gcd_eq_left hd] at h
    exact hp.ne_one h
  · intro h
    rcases hp.2 _ (Nat.gcd_dvd_left p n) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ Nat.gcd_dvd_right p n) h

theorem coprime_of_lt (hp : IsPrime p) {n : Nat} (h0 : n ≠ 0) (hn : n < p) : Nat.Coprime p n :=
  hp.coprime_iff_not_dvd.mpr fun h =>
    Nat.not_le_of_lt hn (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h)

theorem dvd_or_dvd (hp : IsPrime p) {m n : Nat} (h : p ∣ m * n) : p ∣ m ∨ p ∣ n := by
  by_cases hm : p ∣ m
  · exact .inl hm
  · exact .inr (Nat.Coprime.dvd_of_dvd_mul_left (hp.coprime_iff_not_dvd.mpr hm) h)

theorem dvd_of_dvd_pow (hp : IsPrime p) {m : Nat} : ∀ {n : Nat}, p ∣ m ^ n → p ∣ m
  | 0, h => absurd (Nat.eq_one_of_dvd_one h) hp.ne_one
  | _ + 1, h => (hp.dvd_or_dvd (Nat.pow_succ .. ▸ h)).elim hp.dvd_of_dvd_pow id

/-- Every number but 1 has a prime divisor. -/
theorem exists_dvd {n : Nat} (hn : n ≠ 1) : ∃ q, IsPrime q ∧ q ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h0 : n = 0
    · exact ⟨2, ⟨Nat.le_refl 2, fun d hd => by
        have := Nat.le_of_dvd (by decide) hd
        have := Nat.pos_of_dvd_of_pos hd (by decide)
        omega_arith⟩, h0 ▸ Nat.dvd_zero 2⟩
    by_cases h : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n
    · obtain ⟨d, hd, h1, hdn⟩ := h
      obtain ⟨q, hq, hqd⟩ := ih d (Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) hdn) h1
      exact ⟨q, hq, Nat.dvd_trans hqd hd⟩
    · refine ⟨n, ⟨by omega_using [hn, h0], fun d hd => ?_⟩, Nat.dvd_refl n⟩
      exact Classical.byContradiction fun hne => h ⟨d, hd, fun e => hne (.inl e), fun e => hne (.inr e)⟩

end IsPrime

end VG.Proof
