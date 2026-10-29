module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PPrimalityCTState
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.Encoding
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidthCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PTestSmallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PConstructTest
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptBlocksCT
/-! # One complete native p-search iteration has a public trace -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/SearchEntryCT.lean`, which only this module imported.
section

/-! # Enter each p attempt using only the retained public search words -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

private theorem search_attempt_words {p : SearchPublic} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p.plan W s) : PPrimalityWords p.attempt.plan (attemptWords W p.offset) := by
  have h1 := h.slots 1 (by simp [searchSlots])
  have h3 := h.slots 3 (by simp [searchSlots])
  have h4 := h.slots 4 (by simp [searchSlots])
  have h5 := h.slots 5 (by simp [searchSlots])
  have h13 := (h.slots 13 (by simp [searchSlots])).trans p.plan.attempt.tapePtr
  have h15 := (h.slots 15 (by simp [searchSlots])).trans p.plan.attempt.tapeLength
  dsimp only [PPrimalityWords, SearchPublic.attempt, SearchPublic.attemptPlan,
    PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [attemptWords, upd, h1, h3, h4, h5]
  · simpa [attemptWords, upd] using h13
  · simpa [attemptWords, upd] using h15

theorem searchEntry_ready {n pLen qLen : Nat} (H : Spec.Mgf1.Hash) {p : SearchPublic} {s : State}
    (h : SearchBefore n pLen qLen p s) :
    WP isa (.block Impl.Dsa.X86_64.Generation.pAttemptArgs) s
      (PPrimalityBefore n H pLen qLen p.attempt) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, frame, wr, ub, hp, hq⟩ := h
  have entry := hs.entry p.offset p.carry H
  have step := attemptEntry_ok entry ctrl.rdi (ctrl.scr.ld (by decide)) ctrl.offset
  refine WP.mono step fun t ⟨state, ff, hk⟩ => ?_
  have words := search_attempt_words (p := p) hs
  refine ⟨⟨attemptWords W p.offset, words, ?_, frame.congr (hk.gpr (by decide)) hk.2.2, ?_⟩,
    hk.2.2.trans wr, ub, ?_, ?_, hp, hq⟩
  · exact state
  · simpa [SearchPublic.attempt, attemptWords, upd] using hu
  · exact source_of_frame hs.tape ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact p.plan.tapeSeparate _ (by
        change (⟨p.plan.attempt.construct.hash.F, frameBytes⟩ : Region) ∈ searchWrites p.plan.attempt p.plan.C
        simp [searchWrites])) p.plan.attempt.randMax hk.2.1 hk.2.2
  · refine ⟨?_, by rw [hk.2.1, hk.2.2]; exact hs.tapeCover⟩
    simpa [SearchPublic.attempt, SearchPublic.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, attemptWords, upd] using hs.arena.congr hk.2.2

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PPrimalityReadyCT.lean`, which only this module imported.
section

/-! # Construction preserves the public primality inputs and entropy cursor -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.Generation.Layout

theorem pPrimality_ready {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore n H pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pConstruct G pLen qLen) s (PPrimalityAfter p) := by
  obtain ⟨⟨W, hw, hs, _, hu⟩, hwr, hub, tape, ⟨arena, cover⟩, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have step := pConstruct_ok hG hmatch hsize
    (p := q.construct) (hd.trans hq.symm) hs
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
  change WP isa (Impl.Dsa.X86_64.Generation.pConstruct G p.plan.construct.len p.plan.construct.hash.len) s _ at step
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨bt, _, ho, hb, L, ⟨V, R⟩, ws, ptr, ff, rd, wr⟩ => ?_
  have bt' : Spec.Rsa.bytesAt t.mem (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
      p.plan.construct.len = Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value := by
    simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
      PConstructPlan.value, hw.1 5 (by decide)] using bt
  have sq := source_of_frame tape ff q.tapeConstruct p.plan.randMax rd wr
  refine ⟨L, ⟨V, W, R, hw, hu⟩, ws, ?_, bt', ho, hb, ?_, sq, arena.congr wr, by rw [rd, wr]; exact cover,
    wr.trans hwr, hub⟩
  · simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
      hw.1 5 (by decide)] using ptr
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.plan.construct.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
      obtain ⟨r, hr, hc⟩ := hs.pWrite i hi'
      rw [rd, wr]
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      simpa only [PConstructPlan.withWords, HashPlan.withWords, hw.1 5 (by decide)] using hc
    · intro i hi
      rw [List.getElem_eq_getD (0 : Byte), ← bt']
      have hi' : i < p.plan.construct.len := by simpa only [VG.Proof.Dsa.encodeBE_length] using hi
      simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi']
    · intro i hi
      exact p.plan.construct.pOutside i (by simpa only [VG.Proof.Dsa.encodeBE_length] using hi)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PPrimalityCallCT.lean`, which only this module imported.
section

/-! # Instantiate the public width guard and primality call for a p candidate -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Dsa.Generation VG.Impl.Dsa.Generation.Layout

def PPrimalityPublic.width (p : PPrimalityPublic)
    (hb : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)) : CandidateWidthPublic where
  B := p.plan.construct.B
  F := p.plan.construct.hash.F
  Z := p.plan.construct.Z
  w := p.plan.construct.len / 8
  ptr := off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  len := p.plan.construct.len
  value := p.plan.construct.value
  positive := by rcases p.plan.construct.width with h | h | h <;> omega
  fits := by simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb

theorem pPrimality_width {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s) :
    CandidateWidthBefore (p.width h.fits) s := by
  refine ⟨h.ws, h.layout.rsp, h.pointer, h.bytes, ?_⟩
  have read := h.source.rd 0 (by
    rw [VG.Proof.Dsa.encodeBE_length]
    exact (p.width h.fits).positive)
  simpa only [PPrimalityPublic.width, off, BitVec.add_zero] using read

def PPrimalityPublic.primeCall (p : PPrimalityPublic)
    (domain : PDomain p.plan.construct.len p.plan.construct.value) : PrimeTestPublic (8 * p.plan.construct.len) where
  F := p.plan.construct.hash.F
  S := p.plan.construct.hash.S
  A := p.plan.construct.hash.W 5
  rp := p.plan.rp
  rand := p.plan.rand
  N := p.plan.construct.value
  used := p.used
  geometry := (p.plan.call domain).geometry

theorem pPrimality_primeCall {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s)
    (domain : PDomain p.plan.construct.len p.plan.construct.value) :
    PrimeTestBefore (8 * p.plan.construct.len) (p.primeCall domain) s := by
  obtain ⟨V, W, R, hw, hu⟩ := h.frame
  have hc : Impl.Dsa.X86_64.ProbablePrime.candidate (8 * p.plan.construct.len) = Impl.Dsa.Generation.Layout.p := by
    change (if 8 * p.plan.construct.len ≤ 256 then _ else _) = _
    exact ite_eq_right (by rcases p.plan.construct.width with hh | hh | hh <;> omega)
  exact ⟨W, V, {
    layout := h.layout
    rep := R
    arena := hw.1 5 (by decide)
    arenaWrite := h.arena
    tapePtr := hw.2.1
    tapeLength := hw.2.2
    usedSlot := hu
    usedBound := h.usedBound
    tapeSize := p.plan.randMax
    tapeCover := h.tapeCover
    tapeBytes := bytes_of_src h.tape
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len) = _
      rw [h.bytes]
      exact VG.Proof.Dsa.decodeBE_encodeBE (p.width domain.upper).fits
    odd := h.odd
    bitLen := (p.plan.prime domain).bitLength_eq }⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PTestFullCT.lean`, which only this module imported.
section

/-! # Full-width candidates proceed to the probable-prime call -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure PTestFullPublic (len : Nat) where
  width : CandidateWidthPublic
  call : PrimeTestPublic (8 * len)
  full : ¬ width.value < 2 ^ (8 * width.len - 1)

def PTestFullBefore (len : Nat) (p : PTestFullPublic len) (s : State) : Prop :=
  PrimeTestBefore (8 * len) p.call s ∧ CandidateWidthBefore p.width s

theorem pTestFull_ready {len : Nat} {p : PTestFullPublic len} {s : State}
    (h : PTestFullBefore len p s) : WP isa (.block candidateWidth) s fun t =>
      PrimeTestBefore (8 * len) p.call t ∧ t.cf = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  obtain ⟨W, V, hi⟩ := h.1
  exact ⟨⟨W, V, hi.congr hm (hk.gpr (by decide)) hk.2.1 hk.2.2⟩, by simp [cf, p.full]⟩

theorem pTest_full_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest T.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _⟩
    simpa only [eval, hs.1.2, Bool.false_eq_true, Option.some.injEq] using hs.2
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct T
    rcases hlen with rfl | rfl | rfl <;> unfold ProbablePrime.Supported <;> decide

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PPrimalityTestCT.lean`, which only this module imported.
section

/-! # Public width rejection and full-width primality form one native p test -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Dsa.X86_64.Generation

def PPrimalityTestBefore (len : Nat) (p : PPrimalityPublic) (s : State) : Prop :=
  PPrimalityAfter p s ∧ p.plan.construct.len = len

theorem pPrimalityTest_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PPrimalityTestBefore len)) (pTest T.run len) (fun _ _ => True) := by
  intro s t a b s' t' h es et
  obtain ⟨p, ⟨hs, he⟩, ⟨ht, _⟩⟩ := h
  by_cases small : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len - 1)
  · exact pTest_small_ct T.run len s t a b s' t'
      ⟨p.width hs.fits, ⟨pPrimality_width hs, small⟩, ⟨pPrimality_width ht, small⟩⟩ es et
  · let domain : VG.Proof.Dsa.Generation.PDomain p.plan.construct.len p.plan.construct.value :=
      ⟨p.plan.construct.width, hs.odd, Nat.le_of_not_gt small, hs.fits⟩
    subst he
    let full : PTestFullPublic p.plan.construct.len := ⟨p.width hs.fits, p.primeCall domain, small⟩
    have state : ∀ u, PPrimalityAfter p u → PTestFullBefore p.plan.construct.len full u :=
      fun u hu => ⟨pPrimality_primeCall hu domain, pPrimality_width hu⟩
    exact pTest_full_ct T _ hlen s t a b s' t' ⟨full, state s hs, state t ht⟩ es et

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PConstructTestCT.lean`, which only this module imported.
section

/-! # Complete candidate construction, width rejection and primality testing -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem pConstructTest_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore n H pLen qLen))
      (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map PPrimalityPublic.construct (fun _ _ h => pPrimality_construct h)
    (pConstruct_ct hG n hn H pLen qLen sizes hmatch hsize hhash hseedsize hd)) ?_)
    (pPrimalityTest_ct T pLen ?_)
  · intro p s h
    exact WP.mono (pPrimality_ready hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2.2.2.1⟩
  · rcases sizes with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PAttemptTailCT.lean`, which only this module imported.
section

/-! # Return the verified p-test result to the bounded search controller -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

def PPrimalityPublic.returnFrame (p : PPrimalityPublic) : AttemptReturnPublic :=
  ⟨p.plan.construct.hash.F, p.plan.construct.hash.S, p.plan.construct.hash.W 5⟩

theorem pAttemptTail_ready {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (T : PrimeTest) {n pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore n H pLen qLen p s) :
    WP isa (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) s (AttemptReturnBefore p.returnFrame) := by
  obtain ⟨⟨W, hw, hs, _, hu⟩, _, hub, tape, ⟨arena, cover⟩, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have step := pConstructTest_ok hG hmatch hsize T (p := q) (hd.trans hq.symm) hs
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
    hu hub tape (by
      simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
        hw.1 5 (by decide)] using arena) cover
  change WP isa (.seq (pConstruct G p.plan.construct.len p.plan.construct.hash.len)
    (pTest T.run p.plan.construct.len)) s _ at step
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨used, status, V, _, L, R, _⟩ => ?_
  refine ⟨L, V, _, R, ?_⟩
  simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
    VG.Proof.RsaOaep.X86_64.upd, PPrimalityPublic.returnFrame,
    show ¬ (5 : Nat) = 19 by decide, show ¬ (5 : Nat) = 16 by decide, ite_false] using hw.1 5 (by decide)

theorem pAttemptTail_ct {G : Impl.Pbkdf2.Md.X86_64.Stream} (hG : Calls.StreamOK G)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore n H pLen qLen))
      (.seq (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) (.block searchReturn))
      (fun _ _ => True) :=
  RelCT.seq (two_post (pConstructTest_ct hG T n hn H pLen qLen sizes hmatch hsize hhash hseedsize hd)
    (fun _ _ h => pAttemptTail_ready hG T hmatch hsize hhash hseedsize hd h))
    (two_map PPrimalityPublic.returnFrame (fun _ _ h => h) searchReturn_ct)

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem searchBody_ct (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream)
    (T : PrimeTest) (n : Nat) (hn : n = 2 ∨ n = 3) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256))
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore n pLen qLen)) (pAttempt G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold pAttempt
  refine RelCT.seq (two_post (two_map SearchPublic.pointers (fun _ _ h => searchBefore_pointers h)
    pAttemptArgs_ct) (fun _ _ h => searchEntry_ready H h)) ?_
  exact two_map SearchPublic.attempt (fun _ _ h => h)
    (pAttemptTail_ct hG T n hn H pLen qLen sizes hmatch hsize hhash hseedsize hd)

end VG.Proof.Dsa.X86_64.Generation
