module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundStep
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundStepCT

/-! # Public residue squaring stops on the same iteration in both runs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

def roundNextPublic (p : RoundPublic) : RoundPublic := {roundSquared p with count := p.count - 1}

theorem roundLoop_ct (n : Nat) :
    RelCT isa (Two fun p s => 0 < p.count ∧ RoundAt n p s)
      (.loop (roundStep n) .ne) (Two (RoundCoreAt n)) := by
  have loop := RelCT.loop (M := isa) (body := roundStep n) (c := .ne) (Q := Two (RoundCoreAt n))
    (fun k s t => ∃ p, p.count = k ∧ 0 < p.count ∧ RoundAt n p s ∧ RoundAt n p t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop p.count s t ts tt s' t' ⟨p, rfl, hs.1, hs.2, ht.2⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, pos, hs, ht⟩ es et
    obtain ⟨trace, _⟩ := roundStep_ct n _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    obtain ⟨vs, zs, Rs, _, _, os⟩ := wp_result (roundStep_ok hs.1 pos hs.2.2.2 hs.2.2.1) es
    obtain ⟨vt, zt, Rt, _, _, ot⟩ := wp_result (roundStep_ok ht.1 pos ht.2.2.2 ht.2.2.1) et
    rw [hs.2.1] at vs zs
    rw [ht.2.1] at vt zt
    have flags : isa.eval .ne s' = isa.eval .ne t' := by simp only [eval, zs, zt]
    refine ⟨trace, flags, fun _ => ⟨p, Rs, Rt⟩, ?_⟩
    intro more
    have more' : isa.eval .ne t' = some true := flags.symm.trans more
    rcases os with ⟨stop, _⟩ | ⟨_, count, cs, _⟩
    · simp only [eval, stop, Option.map_some, Bool.not_true] at more; cases more
    · rcases ot with ⟨stop, _⟩ | ⟨_, _, ct, _⟩
      · simp only [eval, stop, Option.map_some, Bool.not_true] at more'; cases more'
      · refine ⟨p.count - 1, by omega, roundNextPublic p, rfl, ?_, ?_, ?_⟩
        · change 0 < p.count - 1; omega
        · exact ⟨Rs, vs, cs, by change p.count - 1 < 2 ^ 32; have := hs.2.2.2; omega⟩
        · exact ⟨Rt, vt, ct, by change p.count - 1 < 2 ^ 32; have := ht.2.2.2; omega⟩
end VG.Proof.Dsa.X86.Generation
