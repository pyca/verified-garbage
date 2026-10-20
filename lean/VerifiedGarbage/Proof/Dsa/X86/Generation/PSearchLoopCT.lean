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
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchIterationCT

/-! # The public attempt counter proves bounded p-search trace equivalence -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pSearchLoop_ct {H : Hash} (K : HashOK H) (P : PSearchPlan)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (p : PSearchPublic P) => PAttemptAt P p.counter p.used)
      (.loop (pSearchIteration (pAttempt H P.context.geometry.pLen P.context.geometry.qLen)
        (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1)) .e) (fun _ _ => True) := by
  have loop := RelCT.loop (M := isa)
    (body := pSearchIteration (pAttempt H P.context.geometry.pLen P.context.geometry.qLen)
      (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1)) (c := .e) (Q := fun _ _ => True)
    (fun k s t => ∃ p : PSearchPublic P, k = 32 * P.context.geometry.pLen - p.counter ∧
      PAttemptAt P p.counter p.used s ∧ PAttemptAt P p.counter p.used t) (fun k => ?_)
  · intro s t ts tt s' t' ⟨p, hs, ht⟩ es et
    exact loop (32 * P.context.geometry.pLen - p.counter) s t ts tt s' t' ⟨p, rfl, hs, ht⟩ es et
  · intro s t ts tt s' t' ⟨p, hk, hs, ht⟩ es et
    obtain ⟨trace, _⟩ :=
      pSearchIteration_ct K P digest final hash hashSize _ _ _ _ _ _ ⟨p, hs, ht⟩ es et
    obtain ⟨zs, ns⟩ := wp_result (pSearchIteration_result K digest final hash hashSize hs) es
    obtain ⟨zt, nt⟩ := wp_result (pSearchIteration_result K digest final hash hashSize ht) et
    refine ⟨trace, zs.trans zt.symm, fun _ => trivial, ?_⟩
    intro more
    have again : p.again = true := Option.some.inj (zs.symm.trans more)
    obtain ⟨bs, us, Rs⟩ := ns again
    obtain ⟨_, _, Rt⟩ := nt again
    refine ⟨32 * P.context.geometry.pLen - (p.counter + 1), ?_, ⟨p.counter + 1, p.result.2, bs, us⟩, rfl, Rs, Rt⟩
    omega
end VG.Proof.Dsa.X86.Generation
