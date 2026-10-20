module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePolicy
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeWitnessSpec

/-! # The native witness loop implements DSA's blinded Miller–Rabin policy -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.Proof.RsaKeyGen

def primeRunResult (tape : Spec.RsaKeyGen.Rand) (result : PrimeStepResult) :
    Option (Bool × Spec.RsaKeyGen.Rand) :=
  if result.status = 0 then none else some (result.status == 1, tape.drop result.used)

theorem primeRun_spec {G : PrimeConfig} (mem : Mem) {used uniform i : Nat}
    (seen : uniform < i) (go : uniform < G.checks) :
    primeRunResult (Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen) (primeRun G mem used uniform) =
      Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep G.modulus G.checks G.twos G.exponent)
        (i, uniform) ((Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen).drop used) := by
  let tape := Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen
  have tapeLength : tape.length = G.tapeLen := by simp [tape, Spec.Rsa.bytesAt]
  have drawPos : 0 < G.draw := by have := G.lenMin; unfold PrimeConfig.draw PrimeConfig.n; omega
  rw [mrLoop_step G.modulus G.checks G.twos G.exponent G.draw tape i uniform used
    (.inr go) G.witnessBytes drawPos, tapeLength]
  rw [primeRun]
  by_cases full : used + G.draw ≤ G.tapeLen
  · have witness := primeDrawValue_spec mem full
    rw [ite_eq_left full, ← witness]
    let w := primeDrawValue G mem used
    let passed := Spec.RsaKeyGen.mrIteration G.modulus G.twos G.exponent w.1
    have nextSeen : uniform + w.2.toNat < i + 1 := by
      have h := dsa_round_seen_next seen w.2
      cases hbool : w.2 <;> simp only [hbool, Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false, Bool.toNat_true] at * <;> omega
    by_cases pass : passed = true
    · rw [ite_eq_left pass]
      by_cases more : uniform + w.2.toNat < G.checks
      · have step : primeStepResult G mem used uniform = ⟨4, uniform + w.2.toNat, used + G.draw⟩ := by
          simp only [primeStepResult, full, ite_true, primeResultStatus]
          change (⟨if passed = true then if uniform + w.2.toNat < G.checks then 4 else 1 else 3,
            if passed = true then uniform + w.2.toNat else uniform, used + G.draw⟩ : PrimeStepResult) = _
          simp only [pass, more, ite_true]
        rw [step]
        simp only [dite_true]
        have count : (if w.2 = true then 1 else 0) = w.2.toNat := by cases w.2 <;> rfl
        rw [count]
        exact primeRun_spec mem nextSeen more
      · have step : primeStepResult G mem used uniform = ⟨1, uniform + w.2.toNat, used + G.draw⟩ := by
          simp only [primeStepResult, full, ite_true, primeResultStatus]
          change (⟨if passed = true then if uniform + w.2.toNat < G.checks then 4 else 1 else 3,
            if passed = true then uniform + w.2.toNat else uniform, used + G.draw⟩ : PrimeStepResult) = _
          simp only [pass, more, ite_true, ite_false]
        rw [step]
        simp only [show ¬ (1 : Nat) = 4 by decide, dite_false]
        have done : ¬ (i + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uniform + w.2.toNat < G.checks) := by
          change ¬ (i + 1 ≤ Spec.RsaKeyGen.blindedChecks ∨ uniform + w.2.toNat < Spec.Dsa.primeChecks (8 * G.len))
          rw [dsa_round_continue nextSeen]
          exact more
        have count : (if w.2 = true then 1 else 0) = w.2.toNat := by cases w.2 <;> rfl
        rw [count, mrLoop_done _ _ _ _ _ _ _ done]
        rfl
    · rw [ite_eq_right pass]
      have step : primeStepResult G mem used uniform = ⟨3, uniform, used + G.draw⟩ := by
        simp only [primeStepResult, full, ite_true, primeResultStatus]
        change (⟨if passed = true then if uniform + w.2.toNat < G.checks then 4 else 1 else 3,
          if passed = true then uniform + w.2.toNat else uniform, used + G.draw⟩ : PrimeStepResult) = _
        simp [pass]
      rw [step]
      rfl
  · rw [ite_eq_right full]
    have step : primeStepResult G mem used uniform = ⟨0, uniform, used⟩ := by
      simp only [primeStepResult, full, ite_false]
    rw [step]
    rfl
termination_by G.tapeLen - used
decreasing_by omega
end VG.Proof.Dsa.X86.Generation
