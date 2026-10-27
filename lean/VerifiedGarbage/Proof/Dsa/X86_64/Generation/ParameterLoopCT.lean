module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterTailCT

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterIterationCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # Timing and termination of the complete outer parameter search loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem parameterIteration_ready (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) {n pLen qLen : Nat}
    {p : ParameterPublic} {s : State} (h : ParameterBefore n pLen qLen p s) :
    WP isa (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen)) s
      (ParameterIterationAfter n pLen qLen p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (parameter_check h) fun t ht => ?_)
  refine WP.ite p.exhausted ht.2 (fun he => parameter_exhausted ht (ht.2.trans (congrArg some he))) ?_
  intro he
  have available := parameter_available ht (ht.2.trans (congrArg some he))
  exact WP.seq (WP.mono (parameter_take available) fun _ hv =>
    WP.seq (WP.mono (parameter_body_ready (checkName := checkName) H M Sq T hv) fun _ hw => parameter_status hw))

private def parameterLoopInv (n pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => p.context.seeds.bytes.length - p.seedUsed + 1 = remaining ∧ ParameterBefore n pLen qLen p s

private theorem parameterLoop_step (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) (remaining : Nat) :
    RelCT isa (parameterLoopInv n pLen qLen remaining)
      (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen))
      (fun s t => isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ next < remaining, parameterLoopInv n pLen qLen next s t)) := by
  have step : RelCT isa (parameterLoopInv n pLen qLen remaining)
      (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen))
      (Two fun p s => p.context.seeds.bytes.length - p.seedUsed + 1 = remaining ∧ ParameterIterationAfter n pLen qLen p s) := by
    refine two_post ((parameterIteration_ct (checkName := checkName) H M Sq T n hn pLen qLen sizes).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (parameterIteration_ready (checkName := checkName) H M Sq T h.2) fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have room := (p.next cont).seedBound
  have positive : 0 < p.context.geo.qLen := by rcases p.context.geo.qWidth with hh | hh <;> omega
  refine ⟨p.context.seeds.bytes.length - (p.seedUsed + p.context.geo.qLen) + 1, ?_, p.next cont,
    ⟨rfl, hs.2 cont⟩, rfl, ht.2 cont⟩
  change p.seedUsed + p.context.geo.qLen ≤ p.context.seeds.bytes.length at room
  omega

theorem parameterLoop_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (ParameterBefore n pLen qLen))
      (.loop (tapeIteration seedTape qLen (seedAttempt (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run pLen qLen)) .e) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht⟩ es et
  exact RelCT.loop (parameterLoopInv n pLen qLen) (parameterLoop_step H M Sq T n hn pLen qLen sizes)
    (p.context.seeds.bytes.length - p.seedUsed + 1) s t a b s' t' ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ es et

end VG.Proof.Dsa.X86_64.Generation
