module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBodyReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Framework.Omega

/-! # Retrying a p iteration advances a public counter and an exact witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

def SearchPublic.continues (p : SearchPublic) : Bool :=
  decide (p.status = 3 ∧ p.counter + 1 < 32 * p.plan.attempt.construct.len)

def SearchPublic.next (p : SearchPublic) (h : p.continues = true) : SearchPublic :=
  { p with counter := p.counter + 1, used := p.nextUsed
           bound := (of_decide_eq_true h).2 }

def SearchBodySized (n pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  SearchBodyAfter n p s ∧ p.plan.attempt.construct.len = pLen ∧ p.plan.attempt.construct.hash.len = qLen

def SearchIterationAfter (n pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  eval .e s = some p.continues ∧ ∀ hc : p.continues = true, SearchBefore n pLen qLen (p.next hc) s

theorem searchBody_control {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBodySized n pLen qLen p s) :
    SearchAdvanceBefore (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1) p.control s := by
  refine ⟨h.1.control, ?_, ?_⟩
  · change p.counter < 32 * pLen; rw [← h.2.1]; exact p.bound
  · change p.plan.attempt.construct.hash.count + 1 = _
    rw [p.plan.attempt.construct.hashCount, h.2.1, h.2.2]

theorem searchIteration_tail {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchBodySized n pLen qLen p s)
    (hl : 32 * pLen ≤ 12288) (hs : (8 * pLen - 1) / (8 * qLen) + 1 ≤ 12) :
    WP isa (.seq (.block pSearchStatusCmp)
      (.seq (.ite .e (pSearchAdvance (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) (.block []))
        (.block pSearchStatusCmp))) s (SearchIterationAfter n pLen qLen p) := by
  refine WP.mono (searchTail_ready hl hs (searchBody_control h)) fun t ⟨ct, ff, hk⟩ => ?_
  have condition : eval .e t = some p.continues := by
    simp only [eval, ct.2]
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
  refine ⟨⟨W, mem, used⟩, ?_, h.1.frame.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans h.1.wr, bound, h.2⟩
  have ctrl := ct.1.1
  simpa only [SearchControlPublic.next, SearchPublic.control, SearchPublic.next, retry, ite_true] using ctrl

end VG.Proof.Dsa.X86_64.Generation
