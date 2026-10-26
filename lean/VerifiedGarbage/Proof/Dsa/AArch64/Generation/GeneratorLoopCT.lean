module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchTailCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorIterationCT
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.ToDual

/-! # Timing and termination of the complete generator tape search loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem generatorIteration_ready (M : Mont)  {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchBefore len p s) :
    WP isa (tapeIteration generatorTape len (generatorStep M.mm len)) s
      (GeneratorSearchIterationAfter len p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (generatorSearch_check h) fun t ht => ?_)
  refine WP.ite p.exhausted ht.2 (fun he => generatorSearch_exhausted ht (ht.2.trans (congrArg some he))) ?_
  intro he
  have available := generatorSearch_available ht (ht.2.trans (congrArg some he))
  exact WP.seq (WP.mono (generatorSearch_take available) fun _ hv =>
    WP.seq (WP.mono (generatorSearch_body_ready M hv) fun _ hw => generatorSearch_status hw))

private def generatorLoopInv (len remaining : Nat) : State → State → Prop :=
  Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchBefore len p s

private theorem generatorLoop_step (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (remaining : Nat) :
    RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (fun s t => isa.eval (.zero .x .x0) s = isa.eval (.zero .x .x0) t ∧ (isa.eval (.zero .x .x0) s = some false → True) ∧
        (isa.eval (.zero .x .x0) s = some true → ∃ next < remaining, generatorLoopInv len next s t)) := by
  have step : RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchIterationAfter len p s) := by
    refine two_post ((generatorIteration_ct M len hl).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (generatorIteration_ready M h.2) fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have room := (p.next cont).bound
  have positive : 0 < p.plan.core.len := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine ⟨p.plan.tape.length - (p.used + p.plan.core.len) + 1, ?_, p.next cont,
    ⟨rfl, hs.2 cont⟩, ⟨rfl, ht.2 cont⟩, hsp⟩
  change p.used + p.plan.core.len ≤ p.plan.tape.length at room
  omega

theorem generatorLoop_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (.loop (tapeIteration generatorTape len (generatorStep M.mm len)) (.zero .x .x0)) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht, hsp⟩ es et
  exact RelCT.loop (generatorLoopInv len) (generatorLoop_step M len hl)
    (p.plan.tape.length - p.used + 1) s t a b s' t' ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation
