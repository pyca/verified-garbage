module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStatus
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Public controller counters and status determine every p-search branch -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure SearchControlPublic where
  B : Addr
  counter : Nat
  stride : Nat
  status : Nat
  statusBound : status ≤ 3

def SearchControlBefore (p : SearchControlPublic) (s : State) : Prop :=
  SearchControl p.B p.counter p.stride s ∧ word s.mem p.B 16 = BitVec.ofNat 64 p.status

def SearchControlCompared (p : SearchControlPublic) (s : State) : Prop :=
  SearchControlBefore p s ∧ eval (.zero .x .x3) s = some (decide (p.status = 3))

theorem searchControl_compare {p : SearchControlPublic} {s : State} (h : SearchControlBefore p s) :
    WP isa (.block pSearchStatusCmp) s (SearchControlCompared p) := by
  exact WP.mono (searchStatusCmp_ok h.1 p.statusBound h.2) fun _ ⟨hz, hm, hk⟩ =>
    ⟨⟨h.1.congr hm hk, hm ▸ h.2⟩, hz⟩

theorem searchStatusCmp_ct : RelCT isa (Two SearchControlBefore) (.block pSearchStatusCmp)
    (Two SearchControlCompared) := by
  refine two_post (two_taint [.x0] ?_ (by taint_decide)) (fun _ _ h => searchControl_compare h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr; subst r
  exact hs.1.x0.trans ht.1.x0.symm

def SearchAdvanceBefore (limit stride : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchControlBefore p s ∧ p.counter < limit ∧ p.stride = stride

def SearchAdvanceReady (limit stride : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchControl p.B (p.counter + 1) stride s ∧ eval (.zero .x .x5) s = some (decide (p.counter + 1 < limit))

theorem searchAdvanceHead_ct (limit stride : Nat) (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (pSearchAdvanceHead limit stride)) hc).isSome = true) :
    RelCT isa (Two (SearchAdvanceBefore limit stride)) (.block (pSearchAdvanceHead limit stride))
      (Two (SearchAdvanceReady limit stride)) := by
  refine two_post (two_taint [.x0] ?_ ht) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.1.1.x0.trans ht.1.1.x0.symm
  · intro p s h
    have ctrl : SearchControl p.B p.counter stride s := by rw [← h.2.2]; exact h.1.1
    exact WP.mono (searchAdvanceHead_ok ctrl h.2.1 hl hs) fun t ⟨hc, hf, _, _⟩ => ⟨hc, by
      by_cases he : p.counter + 1 < limit
      · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hf,
          ite_eq_right (show ¬ limit ≤ p.counter + 1 by omega), decide_eq_true he]; rfl
      · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hf,
          ite_eq_left (show limit ≤ p.counter + 1 by omega), decide_eq_false he]; rfl⟩

theorem searchAdvance_ct (limit stride : Nat) (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (pSearchAdvanceHead limit stride)) hc).isSome = true) :
    RelCT isa (Two (SearchAdvanceBefore limit stride)) (pSearchAdvance limit stride) (fun _ _ => True) := by
  refine RelCT.seq (searchAdvanceHead_ct limit stride hl hs ht)
    (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  all_goals
    exact two_taint [.x0] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr; subst r
      exact hs.1.1.x0.trans ht.1.1.x0.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
