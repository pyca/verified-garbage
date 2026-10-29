module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControlCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchTailReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
import VerifiedGarbage.Proof.Framework.Omega
/-! # Retrying a p iteration advances a public counter and an exact witness cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SearchBodyReadyCT.lean`, which only this module imported.
section

/-! # A completed p attempt returns a public status and next witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Proof.RsaOaep.AArch64

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

structure SearchBodyAfter (p : SearchPublic) (s : State) : Prop where
  memory : ∃ W, SearchMemory p.plan W s ∧
    (p.status = 3 → W 16 = BitVec.ofNat 64 p.nextUsed ∧ p.nextUsed ≤ p.plan.attempt.rand.length)
  control : SearchControlBefore p.control s

theorem searchBody_ready (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) {pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) {p : SearchPublic} {s : State}
    (h : SearchBefore pLen qLen p s) :
    WP isa (Impl.Dsa.AArch64.Generation.pAttempt G1 G256 T.run pLen qLen) s (SearchBodyAfter p) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, ub, hp, hq⟩ := h
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
  refine ⟨⟨W', memory, ?_⟩, ⟨ct, wordStatus.trans statusEq⟩⟩
  intro retry
  cases hr : p.result with
  | none => simp [SearchPublic.status, hr] at retry
  | some pair =>
    obtain ⟨b, rest⟩ := pair
    have usedEq : used = p.nextUsed := by simpa only [SearchPublic.nextUsed, hr] using (result b rest hr).2
    exact ⟨usedEq ▸ wordUsed, usedEq ▸ bound⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

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
