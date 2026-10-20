module

public import VerifiedGarbage.Proof.Ffdh.Arm.DomainBody
import VerifiedGarbage.Proof.Ffdh.Arm.CheckPublicSpec
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Data.Nat.ModEq
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Native parameter checks agree with the shared algebraic domain predicate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem modOne_iff {p q : Nat} (positive : 0 < p) (large : 1 < q) :
    p % q = 1 ↔ (p - 1) % q = 0 := by
  constructor
  · intro h
    have reduced := Nat.mod_sub_of_le (a := p) (b := 1) (n := q) (by omega)
    rw [h] at reduced
    exact reduced.symm
  · intro h
    have step : p = (p - 1) + 1 := by omega
    calc
      p % q = ((p - 1) + 1) % q := congrArg (· % q) step
      _ = 1 := by rw [Nat.add_mod, h, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt large]

theorem Inputs.domainG (p : Inputs) : (Spec.Ffdh.domainOf p.k p.dom).g = p.G := rfl

theorem domainValid_native_iff (p : Inputs) : Spec.Ffdh.domainValid p.k p.dom = true ↔
    Spec.Rsa.modulusValid p.P p.k = true ∧ (1 < p.G ∧ p.G < p.P - 1) ∧
      (p.hasQ = true → (2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1) ∧
        p.P % p.Q = 1 ∧ Spec.Rsa.powMod p.G p.Q p.P = 1) := by
  rw [VG.Proof.Ffdh.domainValid_iff, p.domainP, p.domainG, p.domainQ]
  by_cases hasQ : p.hasQ = true
  · rw [ite_eq_left hasQ]
    simp only [Option.some.injEq, forall_eq', hasQ, true_implies]
    constructor
    · rintro ⟨modulus, range, ⟨odd, lower, upper⟩, divides, power⟩
      have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
      refine ⟨modulus, range, ⟨by omega, upper, odd⟩, (modOne_iff (by omega) lower).mpr divides, ?_⟩
      simpa only [VG.Proof.Bignum.powMod_eq] using power
    · rintro ⟨modulus, range, ⟨lower, upper, odd⟩, divides, power⟩
      have facts := VG.Proof.Bignum.valid_facts modulus p.minLength
      refine ⟨modulus, range, ⟨odd, by omega, upper⟩, (modOne_iff (by omega) (by omega)).mp divides, ?_⟩
      simpa only [VG.Proof.Bignum.powMod_eq] using power
  · simp [hasQ]

theorem checkedDomainFlag_spec (p : Inputs) : checkedDomainFlag p =
    if Spec.Ffdh.domainValid p.k p.dom then 1 else 0 := by
  have valid := domainValid_native_iff p
  by_cases modulus : Spec.Rsa.modulusValid p.P p.k = true <;>
    by_cases range : 1 < p.G ∧ p.G < p.P - 1 <;>
    by_cases hasQ : p.hasQ = true <;>
    by_cases qrange : 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 <;>
    by_cases divides : p.P % p.Q = 1 <;>
    by_cases power : Spec.Rsa.powMod p.G p.Q p.P = 1 <;>
    simp_all [checkedDomainFlag, domainMainFlag, domainTailFlag, domainQFlag]

end VG.Proof.Ffdh.Arm
