module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRunSpec
import VerifiedGarbage.Proof.Dsa.Generation.Primality
public import Aesop.BuiltinRules

/-! # Exact status and witness consumption for a trial-cleared candidate -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Generation

theorem primeRun_probablePrime {G : PrimeConfig} (mem : Mem) (used : Nat)
    (large : 3 < G.modulus) (odd : G.modulus % 2 = 1)
    (trial : Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus = false) :
    primeRunResult (Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen) (primeRun G mem used 0) =
      Spec.Dsa.probablePrime G.modulus ((Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen).drop used) := by
  rw [VG.Proof.Dsa.Generation.probablePrime_large large odd]
  change _ = if Spec.RsaKeyGen.obviouslyComposite (Spec.RsaKeyGen.bitLength G.modulus) G.modulus then _ else
    Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep G.modulus (Spec.Dsa.primeChecks (Spec.RsaKeyGen.bitLength G.modulus)) G.twos G.exponent) (1, 0) _
  rw [G.modulusBits, trial]
  simp only [Bool.false_eq_true, ite_false]
  exact primeRun_spec (G := G) mem (used := used) (uniform := 0) (i := 1) (by decide) (by
    unfold PrimeConfig.checks Spec.Dsa.primeChecks
    split <;> decide)

theorem primeStepResult_bounds {G : PrimeConfig} {mem : Mem} {used uniform : Nat}
    (bound : used ≤ G.tapeLen) :
    used ≤ (primeStepResult G mem used uniform).used ∧
      (primeStepResult G mem used uniform).used ≤ G.tapeLen ∧
      ((primeStepResult G mem used uniform).status = 0 ∨ (primeStepResult G mem used uniform).status = 1 ∨
       (primeStepResult G mem used uniform).status = 3 ∨ (primeStepResult G mem used uniform).status = 4) := by
  unfold primeStepResult primeResultStatus
  split
  · rename_i full
    dsimp only
    split
    · split <;> simp_all
    · simp_all
  · simp_all

theorem primeRun_bounds {G : PrimeConfig} {mem : Mem} {used uniform : Nat} (bound : used ≤ G.tapeLen) :
    used ≤ (primeRun G mem used uniform).used ∧ (primeRun G mem used uniform).used ≤ G.tapeLen ∧
      ((primeRun G mem used uniform).status = 0 ∨ (primeRun G mem used uniform).status = 1 ∨
       (primeRun G mem used uniform).status = 3) := by
  have next := primeStepResult_bounds (mem := mem) (uniform := uniform) bound
  rw [primeRun]
  split
  · rename_i more
    have recur := primeRun_bounds (mem := mem) (uniform := (primeStepResult G mem used uniform).uniform) next.2.1
    exact ⟨Nat.le_trans next.1 recur.1, recur.2⟩
  · rename_i done
    exact ⟨next.1, next.2.1, by rcases next.2.2 with h | h | h | h <;> simp_all⟩
termination_by G.tapeLen - used
decreasing_by
  have h := primeStepResult_continue (G := G) (mem := mem) (used := used) (by assumption)
  omega
end VG.Proof.Dsa.X86.Generation
