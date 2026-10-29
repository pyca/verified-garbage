module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControlCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchTailCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
/-! # Retrying a p iteration advances a public counter and an exact witness cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchBodyReadyCT.lean`, which only this module imported.
section

/-! # A completed p attempt returns a public status and next witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.RsaOaep.X86_64

def SearchPublic.result (p : SearchPublic) : Option (Bool × List Byte) :=
  p.plan.stepResult p.counter p.used

def SearchPublic.status (p : SearchPublic) : Nat :=
  match p.result with
  | none => 0
  | some (b, _) => if b then 1 else 3

def SearchPublic.nextUsed (p : SearchPublic) : Nat :=
  match p.result with
  | none => p.used
  | some (_, rest) => p.plan.attempt.rand.length - rest.length

def SearchPublic.control (p : SearchPublic) : SearchControlPublic where
  B := p.plan.C
  counter := p.counter
  stride := p.plan.attempt.construct.hash.count + 1
  status := p.status
  statusBound := by unfold SearchPublic.status; split; decide; split <;> decide

structure SearchBodyAfter (n : Nat) (p : SearchPublic) (s : State) : Prop where
  memory : ∃ W, SearchMemory p.plan W s ∧
    (p.status = 3 → W 16 = BitVec.ofNat 64 p.nextUsed ∧ p.nextUsed ≤ p.plan.attempt.rand.length)
  control : SearchControlBefore p.control s
  frame : FrV n p.plan.attempt.construct.hash.F p.ws s
  wr : s.wr = p.wr

theorem searchBody_ready (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) {p : SearchPublic} {s : State}
    (h : SearchBefore n pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pAttempt G1 G256 T.run pLen qLen) s (SearchBodyAfter n p) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, frame, wr, ub, hp, hq⟩ := h
  subst qLen
  have step := searchBody_ok hG hmatch hsize T hd hhash hseedsize hs ctrl p.bound hu ub
  rw [hp] at step
  refine WP.mono step fun t ⟨ct, W', used, status, memory, bound, wordUsed, _, wordStatus,
    _, _, exhausted, result, _, _, wrt⟩ => ?_
  have statusEq : status = BitVec.ofNat 64 p.status := by
    cases hr : p.result with
    | none => exact (exhausted hr).trans (by simp [SearchPublic.status, hr])
    | some pair =>
      obtain ⟨b, rest⟩ := pair
      exact (result b rest hr).1.trans (by simp [SearchPublic.status, hr])
  refine ⟨⟨W', memory, ?_⟩, ⟨ct, wordStatus.trans statusEq⟩,
    frame.congr (memory.layout.rsp.trans hs.layout.rsp.symm) wrt, wrt.trans wr⟩
  intro retry
  cases hr : p.result with
  | none => simp [SearchPublic.status, hr] at retry
  | some pair =>
    obtain ⟨b, rest⟩ := pair
    have usedEq : used = p.nextUsed := by simpa only [SearchPublic.nextUsed, hr] using (result b rest hr).2
    exact ⟨usedEq ▸ wordUsed, usedEq ▸ bound⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchTailReadyCT.lean`, which only this module imported.
section

/-! # Controller-tail framing and the exact public continuation decision -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem searchTail_ready {limit stride : Nat} (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {p : SearchControlPublic} {s : State} (h : SearchAdvanceBefore limit stride p s) :
    WP isa (.seq (.block pSearchStatusCmp)
      (.seq (.ite .e (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp))) s fun t =>
      SearchControlCompared (p.next limit) t ∧ Outside p.B 0 24 s.mem t.mem ∧ Keep [.rax, .rcx] s t := by
  refine WP.seq (WP.mono (searchStatusCmp_ok h.1.1 p.statusBound h.1.2)
    fun u ⟨uz, um, uk⟩ => ?_)
  have ctrl := h.1.1.congr um uk
  have before : SearchTailCompared limit stride p u := ⟨⟨⟨ctrl, um ▸ h.1.2⟩, h.2⟩, uz⟩
  by_cases retry : p.status = 3
  · refine WP.seq (WP.ite true (by simp [eval, uz, retry]) (fun _ => ?_) (fun he => Bool.noConfusion he))
    have ctrl' : SearchControl p.B p.counter stride u := by rw [← h.2.2]; exact ctrl
    refine WP.mono (searchAdvance_ok ctrl' h.2.1 hl hs) fun v ⟨vc, vs, vf, vk⟩ => ?_
    have next : SearchControlBefore (p.next limit) v := by
      simpa only [SearchControlBefore, SearchControlPublic.next, retry, ite_true, h.2.2] using And.intro vc vs
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, ?_⟩
    · simpa only [tm, um] using vf
    · exact ((uk.trans vk).trans tk).mono (by decide)
  · refine WP.seq (WP.ite false (by simp [eval, uz, retry]) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    have next := searchTail_stop before (by simp [eval, uz, retry])
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, (uk.trans tk).mono (by decide)⟩
    rw [tm, um]; exact Outside.refl _ _ _ _

end VG.Proof.Dsa.X86_64.Generation
end

end

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
