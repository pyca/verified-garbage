module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRunSpec
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedPlan

/-! # A subgroup candidate's public primality result fixes status and continuing tape position -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

def qExpected (P : SearchContextPlan) (T : GenerationTape P.geometry) (used : Nat) :=
  Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) (P.witnesses.bytes.drop used)

def primePublicStatus (expected : Option (Bool × List Byte)) : BitVec 32 :=
  match expected with | none => 0 | some (true, _) => 1 | some (false, _) => 3

def QPhaseAfter (P : SearchContextPlan) (T : GenerationTape P.geometry)
    (len : T.bytes.length = P.geometry.qLen) (seedUsed : BitVec 32) (used : Nat) (s : State) : Prop :=
  ∃ W, ∃ result : PrimeStepResult, PSearchMemory (seedPlan P T len seedUsed) W s ∧
    W 16 = BitVec.ofNat 32 result.used ∧ W 19 = BitVec.ofNat 32 result.status ∧
    result.used ≤ P.witnesses.bytes.length ∧ (result.status = 0 ∨ result.status = 1 ∨ result.status = 3) ∧
    primeRunResult P.witnesses.bytes result = qExpected P T used

theorem qPhaseAfter_view {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {len : T.bytes.length = P.geometry.qLen} {seedUsed : BitVec 32} {used : Nat} {s : State}
    (H : QPhaseAfter P T len seedUsed used s) : SearchFrame s P.geometry.frameBase ∧
      s.mem.readW (off P.geometry.frameBase 76) 32 = primePublicStatus (qExpected P T used) := by
  obtain ⟨W, result, R, _, status, _, statuses, spec⟩ := H
  refine ⟨R.context.arena.frame, ?_⟩
  have word := R.context.representation 19 (by decide)
  change s.mem.readW (off P.geometry.frameBase 76) 32 = W 19 at word
  rw [word, status, ← spec]
  rcases statuses with h | h | h <;> simp [primeRunResult, h, primePublicStatus]

theorem qPhaseAfter_keep {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {len : T.bytes.length = P.geometry.qLen} {seedUsed : BitVec 32} {used : Nat} {s t : State}
    (H : QPhaseAfter P T len seedUsed used s) (mem : t.mem = s.mem) (K : Keeps [.eax] s t) :
    QPhaseAfter P T len seedUsed used t := by
  obtain ⟨W, result, R, cursor, status, bound, statuses, spec⟩ := H
  exact ⟨W, result, R.control (by rw [mem]; exact Outside.refl _ _ _ _) (K.mono (by decide)),
    cursor, status, bound, statuses, spec⟩

theorem qPhaseAfter_success {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {len : T.bytes.length = P.geometry.qLen} {seedUsed : BitVec 32} {used : Nat} {rest : List Byte} {s : State}
    (expected : qExpected P T used = some (true, rest)) (H : QPhaseAfter P T len seedUsed used s) :
    ∃ W, PSearchMemory (seedPlan P T len seedUsed) W s ∧
      W 16 = BitVec.ofNat 32 (P.witnesses.bytes.length - rest.length) := by
  obtain ⟨W, result, R, cursor, _, bound, statuses, spec⟩ := H
  rw [expected] at spec
  rcases statuses with zero | one | three
  · simp [primeRunResult, zero] at spec
  · have tails : P.witnesses.bytes.drop result.used = rest := by simpa [primeRunResult, one] using spec
    have length := congrArg List.length tails
    simp only [List.length_drop] at length
    have eq : result.used = P.witnesses.bytes.length - rest.length := by omega
    exact ⟨W, R, by rw [← eq]; exact cursor⟩
  · simp [primeRunResult, three] at spec
end VG.Proof.Dsa.X86.Generation
