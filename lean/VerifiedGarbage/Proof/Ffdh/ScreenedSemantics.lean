module

public import VerifiedGarbage.Spec.Ffdh.ScreenedCandidate

/-! The early screen preserves both complete probable-prime policies. -/

@[expose] public section
namespace VG.Proof.Ffdh.Screened
open VG.Spec.Ffdh VG.Spec.RsaKeyGen

theorem witnesses_sound {p q : Nat} {r rest : Rand}
    (h : screenedParameterWitnesses p q r = some (true, rest)) :
    ∃ wp wq, probablePrime p wp = true ∧ probablePrime q wq = true := by
  unfold screenedParameterWitnesses at h
  cases ha : drawWitness p r with
  | none => simp only [ha, bind, Option.bind_none] at h; cases h
  | some pair =>
    obtain ⟨a, r1⟩ := pair
    simp only [ha, bind, Option.bind_some] at h
    split at h
    · cases h
    · cases hq : drawWitnesses q (primeChecks (bitLength q)) r1 with
      | none => simp only [hq, Option.bind_none] at h; cases h
      | some pair =>
        obtain ⟨wq, r2⟩ := pair
        simp only [hq, Option.bind_some] at h
        by_cases pass : probablePrime q wq = true
        · simp only [pass, Bool.not_true, Bool.false_eq_true, ite_false] at h
          cases hp : drawWitnesses p (primeChecks (bitLength p) - 1) r2 with
          | none => simp only [hp, Option.bind_none] at h; cases h
          | some pair =>
            obtain ⟨wp, r3⟩ := pair
            simp only [hp, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨a :: wp, wq, h.1, pass⟩
        · have fail := Bool.eq_false_iff.mpr pass
          simp only [fail, Bool.not_false, ite_true, pure, Option.some.injEq, Prod.mk.injEq] at h
          cases h.1

theorem witness_counts {p q : Nat} {r rest : Rand}
    (h : screenedParameterWitnesses p q r = some (true, rest)) :
    ∃ wp wq, wp.length = primeChecks (bitLength p) ∧ wq.length = primeChecks (bitLength q) ∧
      probablePrime p wp = true ∧ probablePrime q wq = true := by
  obtain ⟨wp, wq, hp, hq⟩ := witnesses_sound h
  have lp := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hp).1
  have lq := (Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hq).1
  exact ⟨wp, wq, beq_iff_eq.mp lp.2, beq_iff_eq.mp lq.2, hp, hq⟩

theorem first_failure {p q a : Nat} {r rest : Rand}
    (draw : drawWitness p r = some (a, rest)) (fails : mrRound p a = false) :
    screenedParameterWitnesses p q r = some (false, rest) := by
  simp only [screenedParameterWitnesses, draw, bind, Option.bind_some, fails,
    Bool.not_false, ite_true, pure]

end VG.Proof.Ffdh.Screened
