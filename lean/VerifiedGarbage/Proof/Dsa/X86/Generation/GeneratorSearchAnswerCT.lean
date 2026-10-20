module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchStep
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorBody
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchBodyCT

/-! # A generator body returns the same public status and preserves its tape -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def GeneratorSearchAnswered (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 32 (p.used + p.plan.core.len) ∧
    W 19 = (if p.plan.accepts p.used then 1 else 3)) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_answer {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (H : GeneratorSearchTaken len p s) : WP isa (generatorBody len) s (GeneratorSearchAnswered len p) := by
  have B := generatorSearch_bodyAt H
  obtain ⟨⟨W, R, used, pointer⟩, width, room⟩ := H
  have parent : W 5 = p.plan.parent := (R.fixed 5 (by decide) (by decide)).trans p.plan.savedParent
  rw [← width]
  refine WP.mono (generatorBody_ok p.plan.layout R.prepared R.layout R.representation parent p.plan.base
    (by rw [pointer]; exact B.fit)
    (by intro d hd; rw [pointer]; exact B.read d hd)
    (by rw [pointer]; exact B.apart) R.exponentRead R.outputWrite) fun t ⟨ready, _, Wt, _, O, K⟩ => ?_
  have value : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((W 21).setWidth 64) p.plan.core.len) = p.plan.candidate p.used := by
    rw [pointer]; exact B.value
  rw [value, R.exponentValue] at Wt
  change FrameWords t.mem p.plan.frame (frameUpdate W 19 (if p.plan.accepts p.used then 1 else 3)) at Wt
  have Rt := R.frame ready.prepared Wt (by
    intro i _ hx
    have ne : i ≠ 19 := by intro eq; subst i; simp at hx
    simp only [frameUpdate, ite_eq_right ne]) (generator_body_frame O) K (by decide)
  exact ⟨⟨_, Rt, used, rfl⟩, rfl, room⟩

theorem generatorSearch_answer_ct (len : Nat) : RelCT isa (Two (GeneratorSearchTaken len))
    (generatorBody len) (Two (GeneratorSearchAnswered len)) :=
  two_post (generatorSearch_body_ct len) (fun _ _ H => generatorSearch_answer H)
end VG.Proof.Dsa.X86.Generation
