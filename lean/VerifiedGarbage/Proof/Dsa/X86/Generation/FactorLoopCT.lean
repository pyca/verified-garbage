module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorMath
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Factor
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCTState
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorStepCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Both runs strip exactly the public candidate's trailing zero bits -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def factorNext (p : FactorPublic) : FactorPublic := {p with value := p.value / 2, count := p.count + 1}

theorem factorLoop_ct (n : Nat) (positive : 0 < n) :
    RelCT isa (Two (FactorAt n)) (.loop (factorStep n) .e) (Two FactorScratchAt) := by
  have loop := RelCT.loop (M := isa) (body := factorStep n) (c := .e) (Q := Two FactorScratchAt)
    (fun k s t => ∃ p, p.value = k ∧ FactorAt n p s ∧ FactorAt n p t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop p.value s t ts tt s' t' ⟨p, rfl, hs, ht⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, hs, ht⟩ es et
    obtain ⟨trace, _⟩ := factorStep_ct n _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    have ws := factorStep_ok hs.1 positive hs.2.2.2.1 hs.2.2.2.2.2
    have wt := factorStep_ok ht.1 positive ht.2.2.2.1 ht.2.2.2.2.2
    obtain ⟨bs, vs, zs, _, Ks⟩ := wp_result ws es
    obtain ⟨bt, vt, zt, _, Kt⟩ := wp_result wt et
    rw [hs.2.2.2.2.1] at vs
    rw [ht.2.2.2.2.1] at vt
    rw [vs] at zs
    rw [vt] at zt
    have Ss := hs.1.of_keeps Ks (by decide)
    have St := ht.1.of_keeps Kt (by decide)
    refine ⟨trace, by simp only [eval, zs, zt], fun _ => ⟨p, Ss, St⟩, ?_⟩
    intro more
    have even : p.value / 2 % 2 = 0 := by simpa only [eval, zs, Option.some.injEq, decide_eq_true_eq] using more
    refine ⟨p.value / 2, by have := hs.2.1; omega, factorNext p, rfl, ?_, ?_⟩
    · exact ⟨Ss, (factor_step hs.2.1 hs.2.2.1).1, even, hs.2.2.2.1, vs, bs⟩
    · exact ⟨St, (factor_step ht.2.1 ht.2.2.1).1, even, ht.2.2.2.1, vt, bt⟩
end VG.Proof.Dsa.X86.Generation
