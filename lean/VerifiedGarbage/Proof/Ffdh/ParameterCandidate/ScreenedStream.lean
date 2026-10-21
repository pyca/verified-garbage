module

public import VerifiedGarbage.Spec.Ffdh.ScreenedCandidate
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.Proof.Framework.Omega

/-! The screened policy is three verified witness-engine calls with the original full counts. -/

@[expose] public section
namespace VG.Proof.Ffdh.ParameterCandidate
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen

def screenedChecks (p q : Nat) (r : Rand) : Option (Bool × Rand) := do
  let (pass, r) ← checkWitnesses p 1 r
  if !pass then return (false, r)
  let (pass, r) ← checkWitnesses q (primeChecks (bitLength q)) r
  if !pass then return (false, r)
  checkWitnesses p (primeChecks (bitLength p) - 1) r

theorem prefixed_probable {p a : Nat} {r first tailTape rest : Rand} {wp : List Nat}
    (shape : primeShape p = true) (drawn : drawWitness p r = some (a, first)) (passed : mrRound p a = true)
    (tail : drawWitnesses p (primeChecks (bitLength p) - 1) tailTape = some (wp, rest)) :
    probablePrime p (a :: wp) = wp.all (mrRound p) := by
  have firstBounds := drawWitness_bounds drawn
  have tailBounds := (drawWitnesses_bounds _ _ _ _ tail).2
  have positive : 0 < primeChecks (bitLength p) := by unfold primeChecks; split <;> decide
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    simp only [probablePrime, Bool.and_eq_true] at accepted
    apply List.all_eq_true.mpr
    intro b hb
    have witness := List.all_eq_true.mp accepted.2 b (List.mem_cons_of_mem _ hb)
    exact ((Bool.and_eq_true _ _).mp witness).2
  · intro all
    have count := drawWitnesses_pass_count _ _ _ _ tail all
    have length : (a :: wp).length = primeChecks (bitLength p) := by simp only [List.length_cons]; omega
    simp only [probablePrime, shape, length, beq_self_eq_true, Bool.true_and]
    apply List.all_eq_true.mpr
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨firstBounds, passed⟩
    · have bounds := tailBounds b hb
      have pass := List.all_eq_true.mp all b hb
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨bounds, pass⟩

theorem screenedChecks_eq {p q : Nat} (shapeP : primeShape p = true) (shapeQ : primeShape q = true)
    (r : Rand) : screenedChecks p q r = screenedParameterWitnesses p q r := by
  unfold screenedChecks screenedParameterWitnesses
  rw [checkWitnesses]
  cases drawn : drawWitness p r with
  | none => rfl
  | some pair =>
    obtain ⟨a, first⟩ := pair
    simp only [bind, Option.bind_some]
    cases passed : mrRound p a with
    | false => rfl
    | true =>
      simp only [ite_true, checkWitnesses, Bool.not_true, Bool.false_eq_true,
        ite_false, Option.bind_some, pure]
      rw [checkWitnesses_eq]
      cases qdraw : drawWitnesses q (primeChecks (bitLength q)) first with
      | none => rfl
      | some pair =>
        obtain ⟨wq, afterQ⟩ := pair
        simp only [Option.map_some, Option.bind_some]
        rw [drawWitnesses_probable shapeQ qdraw]
        cases qpass : wq.all (mrRound q) with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          rw [checkWitnesses_eq]
          cases pdraw : drawWitnesses p (primeChecks (bitLength p) - 1) afterQ with
          | none => rfl
          | some pair =>
            obtain ⟨wp, rest⟩ := pair
            simp only [Option.map_some, Option.bind_some]
            rw [prefixed_probable shapeP drawn passed pdraw]

end VG.Proof.Ffdh.ParameterCandidate
