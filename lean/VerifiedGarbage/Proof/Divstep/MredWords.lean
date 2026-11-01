module

public import VerifiedGarbage.Proof.Divstep.SignedWords
public import VerifiedGarbage.Proof.Divstep.Alg

/-!
# One word of Montgomery reduction on signed multiword numbers

`mredRaw p m t` (`Proof/Divstep/Alg.lean`) as code computes it on `t`, a
signed number of `L` words: sign-extended to `L + 1` words, `k p` added for
`k = t₀ m mod 2^64` modulo `2^(64 (L + 1))`, and the words above the lowest
kept (`mred_words`). Signed numbers modulo `2^(64 L)` (`sgn_emod`,
`sgn_of_emod`).
-/

@[expose] public section

namespace VG.Proof.Divstep

theorem pow64_cast (L : Nat) : ((2 ^ (64 * L) : Nat) : Int) = 2 ^ (64 * L) := by push_cast; rfl

/-- `2^(64 L)` and `2^(64 L - 1)` through `H`. -/
theorem pow_H {L : Nat} (hL : 1 ≤ L) : ∃ H : Nat, 2 ^ 63 ≤ H ∧ 2 ^ (64 * L - 1) = H ∧ 2 ^ (64 * L) = 2 * H ∧
    (2 : Int) ^ (64 * L - 1) = H ∧ (2 : Int) ^ (64 * L) = 2 * H := by
  obtain ⟨e, h63⟩ := pow_half hL
  refine ⟨_, h63, rfl, e, by push_cast; rfl, ?_⟩
  rw [← pow64_cast, e]; push_cast; rfl

/-- A signed number is its words modulo `2^(64 L)`. -/
theorem sgn_emod {L x : Nat} (hL : 1 ≤ L) (hx : x < 2 ^ (64 * L)) : sgn L x % 2 ^ (64 * L) = x := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e2] at hx
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [show (x : Int) - 2 * H = x + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by omega)

/-- The signed number of `L` words congruent to `y`, if `y` fits. -/
theorem sgn_of_emod {L x : Nat} {y : Int} (hL : 1 ≤ L)
    (hy₀ : -2 ^ (64 * L - 1) ≤ y) (hy₁ : y < 2 ^ (64 * L - 1)) (h : (x : Int) = y % 2 ^ (64 * L)) :
    sgn L x = y := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  unfold sgn
  simp only [e1, e4]; rw [e3] at hy₀ hy₁; rw [e4] at h
  by_cases hy : 0 ≤ y
  · rw [Int.emod_eq_of_lt hy (by omega)] at h
    rw [ite_eq_left (by omega : x < H)]; exact h
  · rw [show y = (y + 2 * H) + (-1) * (2 * H) by omega, Int.add_mul_emod_self_right,
      Int.emod_eq_of_lt (by omega) (by omega)] at h
    rw [ite_eq_right (by omega : ¬ x < H)]; omega

/-- Sign extension by a word: the top word's sign mask. -/
theorem sext_emod {L S : Nat} (hL : 1 ≤ L) :
    ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) : Int) =
      sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ (64 * (L + 1))) := by
  obtain ⟨e, h63⟩ := pow_half hL
  have e2 : (2 : Int) ^ (64 * (L + 1)) = 2 ^ (64 * L) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
  unfold sgn
  rw [e2]
  split
  · simp
  · push_cast; grind

/-- One word of Montgomery reduction of the signed `L`-word `S` as the code
computes it: `W₁` the sign extension, `k = S₀ m mod 2^64`, `W₂ = W₁ + k p`
modulo `2^(64 (L + 1))`, and `O` its words above the lowest. -/
theorem mred_words {L S W₂ O : Nat} {k p m : Int} (hL : 1 ≤ L)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hk : k = (S % 2 ^ 64 : Nat) * m % 2 ^ 64)
    (hW₂ : (W₂ : Int) = ((S + 2 ^ (64 * L) * (if S < 2 ^ (64 * L - 1) then 0 else 2 ^ 64 - 1) : Nat) + k * p) %
      2 ^ (64 * (L + 1)))
    (hO : W₂ = W₂ % 2 ^ 64 + 2 ^ 64 * O) :
    (O : Int) = mredRaw p m (sgn L S) % 2 ^ (64 * L) := by
  obtain ⟨H, h63, e1, e2, e3, e4⟩ := pow_H hL
  have eQP : (2 : Int) ^ (64 * (L + 1)) = 2 ^ 64 * 2 ^ (64 * L) := by
    rw [Nat.mul_succ, Int.pow_add, Int.mul_comm]
  have eP : (2 : Int) ^ (64 * L) = 2 ^ (64 * L - 64) * 2 ^ 64 := by rw [← Int.pow_add]; congr 1; omega
  set tv := sgn L S with htv
  -- `S ≡ tv` modulo `2^64`.
  have hS64 : ((S % 2 ^ 64 : Nat) : Int) % 2 ^ 64 = tv % 2 ^ 64 := by
    rw [htv, Int.natCast_mod, show ((2 ^ 64 : Nat) : Int) = 2 ^ 64 by rfl, Int.emod_emod]; unfold sgn
    split
    · rfl
    · rw [eP, show (S : Int) - 2 ^ (64 * L - 64) * 2 ^ 64 = S + (-2 ^ (64 * L - 64)) * 2 ^ 64 by grind,
        Int.add_mul_emod_self_right]
  have hk' : k = tv * m % 2 ^ 64 := by
    rw [hk, Int.mul_emod, hS64, ← Int.mul_emod]
  -- `2^64` divides `tv + k p`.
  have hdvd : (2 : Int) ^ 64 ∣ tv + k * p := by
    have h1 : (2 : Int) ^ 64 ∣ tv * (p * m + 1) := Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hm)
    have h2 : (2 : Int) ^ 64 ∣ tv * m - k := by
      rw [hk']; exact Int.dvd_self_sub_emod
    have := Int.dvd_sub h1 (Int.dvd_mul_of_dvd_left (c := p) h2)
    rw [show tv * (p * m + 1) - (tv * m - k) * p = tv + k * p by grind] at this
    exact this
  obtain ⟨R, hR⟩ := hdvd
  have hW : (W₂ : Int) = 2 ^ 64 * (R % 2 ^ (64 * L)) := by
    rw [hW₂, sext_emod hL]
    rw [show sgn L S + (if S < 2 ^ (64 * L - 1) then 0 else (2 : Int) ^ (64 * (L + 1))) + k * p =
      (tv + k * p) + (if S < 2 ^ (64 * L - 1) then 0 else 1) * 2 ^ (64 * (L + 1)) by split <;> grind,
      Int.add_mul_emod_self_right, hR, eQP, Int.mul_emod_mul_of_pos _ _ (by decide)]
  have hmr : mredRaw p m tv = R := by
    unfold mredRaw; rw [← hk', hR, Int.mul_ediv_cancel_left _ (by decide)]
  rw [hmr]
  have h0 : (W₂ % 2 ^ 64 : Nat) = 0 := by
    have : (W₂ : Int) % 2 ^ 64 = 0 := by rw [hW]; exact Int.mul_emod_right _ _
    omega
  rw [h0, Nat.zero_add] at hO
  have : (W₂ : Int) = 2 ^ 64 * O := by rw [hO]; push_cast; rfl
  rw [hW] at this
  exact (Int.eq_of_mul_eq_mul_left (by decide) this).symm

end VG.Proof.Divstep
