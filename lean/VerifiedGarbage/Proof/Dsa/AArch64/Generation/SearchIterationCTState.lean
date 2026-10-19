module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBodyReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
import VerifiedGarbage.Proof.Framework.Omega

/-! # Retrying a p iteration advances a public counter and an exact witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def SearchPublic.continues (p : SearchPublic) : Bool :=
  decide (p.status = 3 ∧ p.counter + 1 < 32 * p.plan.attempt.construct.len)

def SearchPublic.next (p : SearchPublic) (h : p.continues = true) : SearchPublic :=
  { p with counter := p.counter + 1, used := p.nextUsed
           bound := (of_decide_eq_true h).2 }

def SearchBodySized (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  SearchBodyAfter p s ∧ p.plan.attempt.construct.len = pLen ∧ p.plan.attempt.construct.hash.len = qLen

def SearchIterationAfter (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  eval (.zero .x .x3) s = some p.continues ∧ ∀ hc : p.continues = true, SearchBefore pLen qLen (p.next hc) s

theorem searchBody_control {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBodySized pLen qLen p s) :
    SearchAdvanceBefore (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1) p.control s := by
  refine ⟨h.1.control, ?_, ?_⟩
  · change p.counter < 32 * pLen; rw [← h.2.1]; exact p.bound
  · change p.plan.attempt.construct.hash.count + 1 = _
    rw [p.plan.attempt.construct.hashCount, h.2.1, h.2.2]

theorem searchIteration_tail {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBodySized pLen qLen p s)
    (hl : 32 * pLen ≤ 12288) (hs : (8 * pLen - 1) / (8 * qLen) + 1 ≤ 12) :
    WP isa (.seq (.block pSearchStatusCmp)
      (.seq (.ite (.zero .x .x3) (pSearchAdvance (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) (.block []))
        (.block pSearchStatusCmp))) s (SearchIterationAfter pLen qLen p) := by
  refine WP.mono (searchTail_ready hl hs (searchBody_control h)) fun t ⟨ct, ff, hk⟩ => ?_
  have condition : eval (.zero .x .x3) t = some p.continues := by
    rw [ct.2]
    change some (decide ((p.control.next (32 * pLen)).status = 3)) = some p.continues
    simp only [SearchControlPublic.next, SearchPublic.control, SearchPublic.continues]
    rw [h.2.1]
    by_cases retry : p.status = 3 <;> by_cases hc : p.counter + 1 < 32 * pLen <;> simp [retry, hc]
  refine ⟨condition, ?_⟩
  intro cont
  have retry := (of_decide_eq_true cont).1
  obtain ⟨W, memory, cursor⟩ := h.1.memory
  obtain ⟨used, bound⟩ := cursor retry
  have mem := SearchMemory.stable memory ff hk
  refine ⟨⟨W, mem, used⟩, ?_, bound, h.2⟩
  have ctrl := ct.1.1
  simpa only [SearchControlPublic.next, SearchPublic.control, SearchPublic.next, retry, ite_true] using ctrl

end VG.Proof.Dsa.AArch64.Generation
