module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.Generation.Primality
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRunSpec
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeOutcome

/-! # Trial rejection is an immediate composite result with no witness consumption -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG

def primeDecision (G : PrimeConfig) (mem : Mem) (used : Nat) : PrimeStepResult :=
  if Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus then ⟨3, 0, used⟩ else primeRun G mem used 0

theorem primeDecision_spec {G : PrimeConfig} (mem : Mem) (used : Nat)
    (large : 3 < G.modulus) (odd : G.modulus % 2 = 1) :
    primeRunResult (Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen) (primeDecision G mem used) =
      Spec.Dsa.probablePrime G.modulus ((Spec.Rsa.bytesAt mem (G.tape.setWidth 64) G.tapeLen).drop used) := by
  unfold primeDecision
  by_cases trial : Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus = true
  · rw [ite_eq_left trial, VG.Proof.Dsa.Generation.probablePrime_large large odd]
    change _ = if Spec.RsaKeyGen.obviouslyComposite (Spec.RsaKeyGen.bitLength G.modulus) G.modulus then _ else _
    rw [G.modulusBits, trial]
    rfl
  · rw [ite_eq_right trial]
    exact primeRun_probablePrime mem used large odd (Bool.eq_false_iff.mpr trial)
theorem primeDecision_bounds {G : PrimeConfig} {mem : Mem} {used : Nat} (bound : used ≤ G.tapeLen) :
    used ≤ (primeDecision G mem used).used ∧ (primeDecision G mem used).used ≤ G.tapeLen ∧
      ((primeDecision G mem used).status = 0 ∨ (primeDecision G mem used).status = 1 ∨
       (primeDecision G mem used).status = 3) := by
  unfold primeDecision
  split
  · exact ⟨Nat.le_refl _, bound, Or.inr (Or.inr rfl)⟩
  · exact primeRun_bounds bound
end VG.Proof.Dsa.X86.Generation
