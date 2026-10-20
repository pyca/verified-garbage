module
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorIterationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorIterationResultCT

/-! # Every generator retry consumes a positive complete tape chunk -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorLoop_ct (len : Nat) : RelCT isa (Two (GeneratorSearchBefore len))
    (.loop (tapeIteration generatorTape len (generatorBody len)) .e) (fun _ _ => True) := by
  have loop := RelCT.loop (M := isa) (body := tapeIteration generatorTape len (generatorBody len))
    (c := .e) (Q := fun _ _ => True)
    (fun k s t => ∃ p, k = p.plan.tape.length - p.used ∧
      GeneratorSearchBefore len p s ∧ GeneratorSearchBefore len p t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop (p.plan.tape.length - p.used) s t ts tt s' t' ⟨p, rfl, hs, ht⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, hs, ht⟩ es et
    obtain ⟨trace, _⟩ := generatorIteration_ct len _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    obtain ⟨zs, nextS⟩ := wp_result (generatorIteration_result hs) es
    obtain ⟨zt, nextT⟩ := wp_result (generatorIteration_result ht) et
    refine ⟨trace, zs.trans zt.symm, fun _ => trivial, ?_⟩
    intro more
    have again : p.again = true := Option.some.inj (zs.symm.trans more)
    obtain ⟨bs, Rs⟩ := nextS again
    obtain ⟨bt, Rt⟩ := nextT again
    refine ⟨p.plan.tape.length - (p.used + p.plan.core.len), ?_, ⟨p.plan, p.used + p.plan.core.len, bs⟩, rfl, Rs, Rt⟩
    have := p.plan.core.lenMin
    omega
end VG.Proof.Dsa.X86.Generation
