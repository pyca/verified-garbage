module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttemptAnswerCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchTailResultCT

/-! # Each public rejection either advances the p-search or exhausts its attempt budget -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def PSearchPublic.again {P : PSearchPlan} (p : PSearchPublic P) : Bool :=
  decide (p.result.1 = 3 ∧ p.counter + 1 < 32 * P.context.geometry.pLen)

def PSearchIterationResult (P : PSearchPlan) (p : PSearchPublic P) (s : State) : Prop :=
  eval .e s = some p.again ∧ (p.again = true →
    ∃ (_bound : p.counter + 1 < 32 * P.context.geometry.pLen) (_usedBound : p.result.2 ≤ P.context.witnesses.bytes.length),
      PAttemptAt P (p.counter + 1) p.result.2 s)

theorem pSearchTail_result {P : PSearchPlan} {p : PSearchPublic P} {s : State}
    (H : PAttemptAnswered P p s) :
    WP isa (searchTail (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1)) s
      (PSearchIterationResult P p) := by
  obtain ⟨⟨W, used, R, cursor, usedBound, usedEq⟩, tail⟩ := H
  refine WP.mono (searchTail_result tail) fun t ⟨Ct, zf, O, K⟩ => ?_
  have z : (p.tail.nextStatus (32 * P.context.geometry.pLen) = 3) ↔
      p.result.1 = 3 ∧ p.counter + 1 < 32 * P.context.geometry.pLen := by
    by_cases retry : p.result.1 = 3
    · by_cases more : p.counter + 1 < 32 * P.context.geometry.pLen <;>
        simp [SearchTailPublic.nextStatus, PSearchPublic.tail, retry, more]
    · simp [SearchTailPublic.nextStatus, PSearchPublic.tail, retry]
  refine ⟨?_, ?_⟩
  · change t.zf = some p.again
    rw [zf]
    unfold PSearchPublic.again
    simp only [z]
  · intro again
    have facts : p.result.1 = 3 ∧ p.counter + 1 < 32 * P.context.geometry.pLen := of_decide_eq_true again
    have eq : used = p.result.2 := usedEq (by omega)
    refine ⟨facts.2, eq ▸ usedBound, ⟨W, R.control O K, ?_⟩, ?_⟩
    · rw [← eq]; exact cursor
    · simpa only [SearchTailPublic.nextCounter, PSearchPublic.tail, facts.1, ite_true] using Ct

theorem pSearchIteration_result {H : Hash} (K : HashOK H) {P : PSearchPlan} {p : PSearchPublic P}
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length)
    {s : State} (R : PAttemptAt P p.counter p.used s) :
    WP isa (pSearchIteration (pAttempt H P.context.geometry.pLen P.context.geometry.qLen)
      (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1)) s (PSearchIterationResult P p) :=
  WP.seq (WP.mono (pAttempt_answer K digest final hash hashSize R) fun _ h => pSearchTail_result h)

theorem pSearchIteration_ct {H : Hash} (K : HashOK H) (P : PSearchPlan)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (p : PSearchPublic P) => PAttemptAt P p.counter p.used)
      (pSearchIteration (pAttempt H P.context.geometry.pLen P.context.geometry.qLen)
        (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1))
      (Two (PSearchIterationResult P)) := by
  refine RelCT.seq (pAttempt_answer_ct K P digest final hash hashSize)
    (two_post (two_map PSearchPublic.tail (fun _ _ h => h.2)
      (searchTail_ct _ _)) (fun _ _ h => pSearchTail_result h))
end VG.Proof.Dsa.X86.Generation
