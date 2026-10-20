module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchAnswerCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeState

/-! # Public retry decisions and decreasing generator-tape remainder -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def GeneratorSearchPublic.again (p : GeneratorSearchPublic) : Bool :=
  Bool.not p.exhausted && decide (¬ p.plan.accepts p.used)

def GeneratorIterationResult (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  eval .e s = some p.again ∧ (p.again = true → ∃ bound : p.used + p.plan.core.len ≤ p.plan.tape.length,
    GeneratorSearchBefore len ⟨p.plan, p.used + p.plan.core.len, bound⟩ s)

theorem generatorIteration_result {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchBefore len p s) :
    WP isa (tapeIteration generatorTape len (generatorBody len)) s (GeneratorIterationResult len p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (generatorSearch_check H) fun a A => ?_)
  by_cases exhausted : p.plan.tape.length - p.used < p.plan.core.len
  · have again : p.again = false := by simp [GeneratorSearchPublic.again, GeneratorSearchPublic.exhausted, exhausted]
    refine WP.ite true (by change a.cf = some true; simpa [GeneratorSearchPublic.exhausted, exhausted] using A.2)
      (fun _ => ?_) (fun he => Bool.noConfusion he)
    obtain ⟨⟨W, R, _⟩, _⟩ := A.1
    refine WP.mono (tapeExhausted_ok R.layout R.representation) fun t ⟨zf, _, _, _, _⟩ => ?_
    exact ⟨by simpa only [eval, again] using zf, by simp only [again, Bool.false_eq_true, false_implies]⟩
  · have available : GeneratorSearchAvailable len p a := ⟨A.1, by have := p.bound; omega⟩
    refine WP.ite false (by change a.cf = some false; simpa [GeneratorSearchPublic.exhausted, exhausted] using A.2)
      (fun he => Bool.noConfusion he) (fun _ => ?_)
    refine WP.seq (WP.mono (generatorSearch_take available) fun b B => ?_)
    refine WP.seq (WP.mono (generatorSearch_answer B) fun c C => ?_)
    obtain ⟨⟨W, R, used, status⟩, width, room⟩ := C
    refine WP.mono (tapeStatus_ok R.layout R.representation) fun t ⟨zf, mem, K⟩ => ?_
    refine ⟨?_, fun _ => ⟨room, ⟨W, R.congr mem K (by decide), used⟩, width⟩⟩
    change t.zf = some p.again
    rw [zf, status]
    simp only [GeneratorSearchPublic.again, GeneratorSearchPublic.exhausted, exhausted, decide_false,
      Bool.not_false, Bool.true_and]
    by_cases accepted : p.plan.accepts p.used <;> simp [accepted]
end VG.Proof.Dsa.X86.Generation
