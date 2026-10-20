module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRun
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeTestFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeStepCT

/-! # Each continuing primality iteration consumes a positive public draw -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem primeLoopBody_ct (G : PrimeConfig) : RelCT isa (Two (PrimeLoopAt G))
    (.loop (primeStep G.len G.draw G.checks) .e) (fun _ _ => True) := by
  have loop := RelCT.loop (M := isa) (body := primeStep G.len G.draw G.checks) (c := .e) (Q := fun _ _ => True)
    (fun k s t => ∃ p, k = G.tapeLen - p.used ∧ PrimeLoopAt G p s ∧ PrimeLoopAt G p t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop (G.tapeLen - p.used) s t ts tt s' t' ⟨p, rfl, hs, ht⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, hs, ht⟩ es et
    obtain ⟨trace, _⟩ := primeStep_ct G _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    obtain ⟨Rs, zs, _, cs, us, Fs, _⟩ := wp_result (primeStep_ok hs.ready p.usedBound p.bound hs.used hs.count) es
    obtain ⟨Rt, zt, _, ct, ut, Ft, _⟩ := wp_result (primeStep_ok ht.ready p.usedBound p.bound ht.used ht.count) et
    rw [hs.stepResult] at zs cs us
    rw [ht.stepResult] at zt ct ut
    refine ⟨trace, by simp only [eval, zs, zt], fun _ => trivial, ?_⟩
    intro more
    have status : (primePublicStep G p).status = 4 := by
      simpa only [eval, zs, Option.some.injEq, decide_eq_true_eq] using more
    have progress := primeStepResult_continue (G := G) (mem := s.mem) (used := p.used) (uniform := p.uniform)
      (by rw [hs.stepResult]; exact status)
    rw [hs.stepResult] at progress
    let q : PrimeLoopPublic G := ⟨p.tape, (primePublicStep G p).used, (primePublicStep G p).uniform,
      progress.2.1, progress.2.2⟩
    refine ⟨G.tapeLen - q.used, ?_, q, rfl, ?_, ?_⟩
    · dsimp only [q]; omega
    · exact ⟨Rs, us, cs, Fs.testFrame.tape.trans hs.tape⟩
    · exact ⟨Rt, ut, ct, Ft.testFrame.tape.trans ht.tape⟩
end VG.Proof.Dsa.X86.Generation
