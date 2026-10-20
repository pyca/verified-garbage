module
public import VerifiedGarbage.Spec.Dsa

/-! # DSA's uniform-witness requirement subsumes the blinded minimum

The native loop need only count uniform witnesses: DSA requires at least
64, already more than the 16-round blinded minimum. Since a draw adds at
most one uniform witness, reaching that count also satisfies the minimum
number of rounds. Random-tape consumption is unchanged.
-/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

theorem dsa_checks_minimum (bits : Nat) : Spec.RsaKeyGen.blindedChecks < Spec.Dsa.primeChecks bits := by
  unfold Spec.RsaKeyGen.blindedChecks Spec.Dsa.primeChecks
  split <;> omega

theorem dsa_round_continue {bits i uniform : Nat} (seen : uniform < i) :
    (i ≤ Spec.RsaKeyGen.blindedChecks ∨ uniform < Spec.Dsa.primeChecks bits) ↔
      uniform < Spec.Dsa.primeChecks bits := by
  have := dsa_checks_minimum bits
  omega

theorem dsa_round_seen_next {i uniform : Nat} (seen : uniform < i) (isUniform : Bool) :
    uniform + (if isUniform then 1 else 0) < i + 1 := by
  cases isUniform <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
end VG.Proof.Dsa.X86.Generation
