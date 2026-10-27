module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterTailCT

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ParameterIterationCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Timing and termination of the complete outer parameter search loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.MillerRabin.AArch64

theorem parameterIteration_ready (H : GenerationHashes) (M : Mont)  (T : PrimeTest) {pLen qLen : Nat}
    {p : ParameterPublic} {s : State} (h : ParameterBefore pLen qLen p s) :
    WP isa (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm T.run pLen qLen)) s
      (ParameterIterationAfter pLen qLen p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (parameter_check h) fun t ht => ?_)
  refine WP.ite p.exhausted ht.2 (fun he => parameter_exhausted ht (ht.2.trans (congrArg some he))) ?_
  intro he
  have available := parameter_available ht (ht.2.trans (congrArg some he))
  exact WP.seq (WP.mono (parameter_take available) fun _ hv =>
    WP.seq (WP.mono (parameter_body_ready H M T hv) fun _ hw => parameter_status hw))

private def parameterLoopInv (pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => p.context.seeds.bytes.length - p.seedUsed + 1 = remaining ∧ ParameterBefore pLen qLen p s

private theorem parameterLoop_step (H : GenerationHashes) (M : Mont)  (T : PrimeTest) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) (remaining : Nat) :
    RelCT isa (parameterLoopInv pLen qLen remaining)
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm T.run pLen qLen))
      (fun s t => isa.eval (.zero .x .x0) s = isa.eval (.zero .x .x0) t ∧ (isa.eval (.zero .x .x0) s = some false → True) ∧
        (isa.eval (.zero .x .x0) s = some true → ∃ next < remaining, parameterLoopInv pLen qLen next s t)) := by
  have step : RelCT isa (parameterLoopInv pLen qLen remaining)
      (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm T.run pLen qLen))
      (Two fun p s => p.context.seeds.bytes.length - p.seedUsed + 1 = remaining ∧ ParameterIterationAfter pLen qLen p s) := by
    refine two_post ((parameterIteration_ct H M T pLen qLen sizes).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (parameterIteration_ready H M T h.2) fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have room := (p.next cont).seedBound
  have positive : 0 < p.context.geo.qLen := by rcases p.context.geo.qWidth with hh | hh <;> omega
  refine ⟨p.context.seeds.bytes.length - (p.seedUsed + p.context.geo.qLen) + 1, ?_, p.next cont,
    ⟨rfl, hs.2 cont⟩, ⟨rfl, ht.2 cont⟩, hsp⟩
  change p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length at room
  omega

theorem parameterLoop_ct (H : GenerationHashes) (M : Mont)  (T : PrimeTest) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterBefore pLen qLen))
      (.loop (tapeIteration seedTape qLen (seedAttempt H.sha1 H.sha256 M.mm T.run pLen qLen)) (.zero .x .x0)) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht, hsp⟩ es et
  exact RelCT.loop (parameterLoopInv pLen qLen) (parameterLoop_step H M T pLen qLen sizes)
    (p.context.seeds.bytes.length - p.seedUsed + 1) s t a b s' t' ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation
