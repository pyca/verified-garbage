module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControlCT
import VerifiedGarbage.Proof.Framework.Omega

/-! # The controller tail determines whether the bounded p loop continues -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def SearchControlPublic.next (p : SearchControlPublic) (limit : Nat) : SearchControlPublic where
  B := p.B
  counter := if p.status = 3 then p.counter + 1 else p.counter
  stride := p.stride
  status := if p.status = 3 then (if p.counter + 1 < limit then 3 else 2) else p.status
  statusBound := by split; split <;> decide; exact p.statusBound

def SearchTailCompared (limit stride : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchAdvanceBefore limit stride p s ∧ eval (.zero .x .x3) s = some (decide (p.status = 3))

theorem searchTail_compare {limit stride : Nat} {p : SearchControlPublic} {s : State}
    (h : SearchAdvanceBefore limit stride p s) :
    WP isa (.block pSearchStatusCmp) s (SearchTailCompared limit stride p) :=
  WP.mono (searchControl_compare h.1) fun _ ht => ⟨⟨ht.1, h.2⟩, ht.2⟩

theorem searchTail_advance {limit stride : Nat} (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {p : SearchControlPublic} {s : State} (h : SearchTailCompared limit stride p s)
    (he : eval (.zero .x .x3) s = some true) :
    WP isa (pSearchAdvance limit stride) s (SearchControlBefore (p.next limit)) := by
  have retry : p.status = 3 := by simpa only [Option.some.injEq, decide_eq_true_eq] using h.2.symm.trans he
  have ctrl : SearchControl p.B p.counter stride s := by rw [← h.1.2.2]; exact h.1.1.1
  refine WP.mono (searchAdvance_ok ctrl h.1.2.1 hl hs) fun t ⟨hc, status, _, _⟩ => ?_
  change SearchControl p.B (if p.status = 3 then p.counter + 1 else p.counter) p.stride t ∧
    word t.mem p.B 16 = BitVec.ofNat 64 (if p.status = 3 then (if p.counter + 1 < limit then 3 else 2) else p.status)
  simpa only [retry, ite_true, h.1.2.2] using And.intro hc status

theorem searchTail_stop {limit stride : Nat} {p : SearchControlPublic} {s : State}
    (h : SearchTailCompared limit stride p s) (he : eval (.zero .x .x3) s = some false) :
    SearchControlBefore (p.next limit) s := by
  have retry : ¬ p.status = 3 := by simpa only [Option.some.injEq, decide_eq_false_iff_not] using h.2.symm.trans he
  simpa only [SearchControlBefore, SearchControlPublic.next, retry, ite_false] using h.1.1

theorem searchTail_ct (limit stride : Nat) (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0]) (.block (pSearchAdvanceHead limit stride)) hc).isSome = true) :
    RelCT isa (Two (SearchAdvanceBefore limit stride))
      (.seq (.block pSearchStatusCmp)
        (.seq (.ite (.zero .x .x3) (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp)))
      (Two (fun (p : SearchControlPublic) s => SearchControlCompared (p.next limit) s)) := by
  refine RelCT.seq (two_post (searchStatusCmp_ct.mono
    (fun _ _ => two_mono fun _ _ h => h.1) (fun _ _ _ => True.intro))
    (fun _ _ h => searchTail_compare h)) (RelCT.seq (R := Two (fun (p : SearchControlPublic) s => SearchControlBefore (p.next limit) s)) ?_ ?_)
  · refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
    · exact two_post ((searchAdvance_ct limit stride hl hs ht).mono
        (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ _ => True.intro))
        (fun _ _ h => searchTail_advance hl hs h.1 h.2)
    · exact RelCT.block_nil (fun _ _ => two_mono fun _ _ h => searchTail_stop h.1 h.2)
  · exact two_post ((two_map (fun p : SearchControlPublic => p.next limit) (fun _ _ h => h) searchStatusCmp_ct).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => searchControl_compare h)

end VG.Proof.Dsa.AArch64.Generation
