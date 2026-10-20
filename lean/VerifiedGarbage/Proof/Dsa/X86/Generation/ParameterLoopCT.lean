module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterCTState
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterIterationCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterIterationResultCT

/-! # Every public outer-loop retry consumes a nonempty seed chunk -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem parameterLoop_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (plen qlen : Nat) (digest : H.D = qlen) (final : H.F = qlen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * qlen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * qlen) bs).length = qlen) :
    RelCT isa (Two (ParameterBefore plen qlen))
      (.loop (tapeIteration seedTape qlen (parameterBody H plen qlen (finishDomain F.name F.code plen qlen))) .e)
      (fun _ _ => True) := by
  have loop := RelCT.loop (M := isa)
    (body := tapeIteration seedTape qlen (parameterBody H plen qlen (finishDomain F.name F.code plen qlen)))
    (c := .e) (Q := fun _ _ => True)
    (fun k s t => ∃ p, k = p.plan.seeds.bytes.length - p.seedUsed ∧
      ParameterBefore plen qlen p s ∧ ParameterBefore plen qlen p t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop (p.plan.seeds.bytes.length - p.seedUsed) s t ts tt s' t' ⟨p, rfl, hs, ht⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, hs, ht⟩ es et
    obtain ⟨trace, _⟩ := parameterIteration_ct K F plen qlen digest final hash hashSize _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    obtain ⟨zs, nextS⟩ := wp_result (parameterIteration_result K F digest final hash hashSize hs) es
    obtain ⟨zt, nextT⟩ := wp_result (parameterIteration_result K F digest final hash hashSize ht) et
    refine ⟨trace, zs.trans zt.symm, fun _ => trivial, ?_⟩
    intro more
    have again : p.again = true := Option.some.inj (zs.symm.trans more)
    obtain ⟨bs, Rs⟩ := nextS again
    obtain ⟨bt, Rt⟩ := nextT again
    refine ⟨p.plan.seeds.bytes.length - (p.seedUsed + p.plan.geometry.qLen), ?_,
      ⟨p.plan, p.seedUsed + p.plan.geometry.qLen, p.nextUsed, bs, p.nextBound⟩, rfl, Rs, Rt⟩
    have := p.plan.geometry.qWidth
    omega
end VG.Proof.Dsa.X86.Generation
