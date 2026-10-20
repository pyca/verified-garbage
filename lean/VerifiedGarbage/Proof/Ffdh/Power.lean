module

public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Domain

/-! # Powers of a checked FFDH generator remain in its subgroup -/

@[expose] public section

namespace VG.Proof.Ffdh

open VG.Spec.Ffdh

/-- No primality assumption is needed for closure of the generator's subgroup. -/
theorem power_subgroup {g p q x : Nat} (hg : g ^ q % p = 1) : (g ^ x % p) ^ q % p = 1 % p := by
  rw [← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm x q, Nat.pow_mul, Nat.pow_mod, hg, Nat.one_pow]

/-- The domain's algebraic checks include validity of its generator. -/
theorem parametersValid_generator {a : Parameters} (h : parametersValid a = true) :
    publicValid ⟨a, a.g⟩ = true := by
  unfold parametersValid at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold publicValid
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨h.1.1.2, h.1.2⟩, ?_⟩
  cases hq : a.q with
  | none => rfl
  | some q =>
    have hh := h.2
    rw [hq] at hh
    simp only [Bool.and_eq_true] at hh
    exact hh.2

/-- Given valid parameters, a generated power needs only the range check;
the optional q-membership check follows from `g^q mod p = 1`. -/
theorem publicValid_power {a : Parameters} (h : parametersValid a = true) (x : Nat) :
    publicValid ⟨a, a.g ^ x % a.p⟩ = true ↔ 1 < a.g ^ x % a.p ∧ a.g ^ x % a.p < a.p - 1 := by
  have hg := (publicValid_eq a a.g).mp (parametersValid_generator h)
  rw [publicValid_eq]
  constructor
  · exact And.left
  · intro hr
    refine ⟨hr, fun q hq => ?_⟩
    have hp : 1 < a.p := by have := hg.1; omega
    rw [power_subgroup (hg.2 q hq), Nat.mod_eq_of_lt hp]

end VG.Proof.Ffdh
