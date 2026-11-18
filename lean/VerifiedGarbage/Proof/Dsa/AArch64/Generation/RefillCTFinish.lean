module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Impl.RsaOaep.AArch64
import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Impl.RsaOaep.AArch64
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillLoop
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Refill
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStage
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillOutcome
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedCTState
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorCall
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generator.ABI
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import Mathlib.Tactic.Push
public import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SeedSearchPlanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.NativeGeneratorCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryTape
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
meta import Mathlib.Tactic.Push
meta import Mathlib.Data.Nat.Basic
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCT
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchCTState
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchStable
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
public import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchControl
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PAttempt
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Spec.Dsa
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructTest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeCallCT
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillAttempt
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OnSuccessCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
meta import VerifiedGarbage.Proof.Dsa.Generation.GeneratorCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashChoice

/-! ### `Dsa.AArch64.Generation.RefillCTLoop`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.RefillCTAttempt`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.SeedPhaseStableCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.SearchIterationCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.SearchBodyCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PTestSmallCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.CandidateWidthCT`, which this module and modules that import it used -/

section

/-! # The candidate-width guard has public addressing and a public decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation

structure CandidateWidthPublic where
  B : Addr
  F : Addr
  Z : Nat
  w : Nat
  ptr : Addr
  len : Nat
  value : Nat
  positive : 0 < len
  fits : value < 256 ^ len

structure CandidateWidthBefore (p : CandidateWidthPublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  stack : s.sp = p.F
  pointer : word s.mem p.B 160 = p.ptr
  bytes : Spec.Rsa.bytesAt s.mem p.ptr p.len = Spec.Dsa.encodeBE p.len p.value
  read : InRegions (s.rd ++ s.wr) p.ptr 1

def CandidateWidthAfter (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ eval (.zero .x .x3) s = some (decide (p.value < 2 ^ (8 * p.len - 1)))

theorem candidateWidth_ready {p : CandidateWidthPublic} {s : State} (h : CandidateWidthBefore p s) :
    WP isa (.block candidateWidth) s (CandidateWidthAfter p) := by
  refine WP.mono (candidateWidth_ok h.ws h.pointer p.positive p.fits h.bytes h.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  have ws : Ws t p.B p.Z p.w := by
    refine ⟨h.ws.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.ws.x0,
      hm ▸ h.ws.hw, hm ▸ h.ws.hS, ?_, h.ws.hZ, h.ws.w1, h.ws.w2⟩
    intro j hj; rw [hm]; exact h.ws.harr j hj
  exact ⟨⟨ws, hk.sp.trans h.stack, hm ▸ h.pointer,
    hm ▸ h.bytes, (by rw [hk.rd, hk.wr]; exact h.read)⟩, cf⟩

theorem candidateWidth_ct : RelCT isa (Two CandidateWidthBefore) (.block candidateWidth)
    (Two CandidateWidthAfter) := by
  refine two_post ?_ (fun _ _ h => candidateWidth_ready h)
  apply RelCT.block_append (M := isa) (l₁ := [VG.Impl.Bignum.AArch64.ldh .x1 20])
    (l₂ := [.ldrb .x3 .x1 0, .lsr .x .x3 .x3 7])
  refine RelCT.seq (two_post (Ψ := fun (p : CandidateWidthPublic) s => s.gpr .x1 = p.ptr)
    (two_taint [.x0] ?_ (by taint_decide)) ?_) (two_taint [.x1] ?_ (by taint_decide))
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.ws.x0.trans ht.ws.x0.symm
  · intro p s h
    have ld := h.ws.scr.ld (d := 160) (show 160 + 8 ≤ p.Z from Nat.le_trans (by decide) h.ws.h256)
    brun [h.ws.x0, hdr_enc (by decide : 20 < 32), ld, h.pointer]
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.trans ht.symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Width rejection has a fixed trace and does not enter primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def PTestSmallBefore (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ p.value < 2 ^ (8 * p.len - 1)

theorem pTest_small_ct (prime : Nat → Prog isa) (len : Nat) :
    RelCT isa (Two PTestSmallBefore) (pTest prime len) (fun _ _ => True) := by
  unfold pTest
  have guard : RelCT isa (Two PTestSmallBefore) (.block candidateWidth)
      (Two (fun (p : CandidateWidthPublic) s => s.sp = p.F ∧ eval (.zero .x .x3) s = some true)) := by
    refine two_post (candidateWidth_ct.mono (fun _ _ => two_mono fun _ _ h => h.1)
      (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (candidateWidth_ready h.1) fun _ ht => ⟨ht.1.stack, by simpa only [decide_eq_true h.2] using ht.2⟩
  refine RelCT.seq guard (two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _, _⟩
    cases Option.some.inj (hs.1.2.symm.trans hs.2)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SearchEntryCT`, which only this module used -/

section

/-! # Enter each p attempt using only the retained public search words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

private theorem search_attempt_words {p : SearchPublic} {W : Nat → BitVec 64} {s : State}
    (h : SearchMemory p.plan W s) : PPrimalityWords p.attempt.plan (attemptWords W p.offset) := by
  have h1 := h.slots 1 (by simp [searchSlots])
  have h3 := h.slots 3 (by simp [searchSlots])
  have h4 := h.slots 4 (by simp [searchSlots])
  have h5 := h.slots 5 (by simp [searchSlots])
  have h14 := (h.slots 14 (by simp [searchSlots])).trans p.plan.attempt.tapePtr
  have h15 := (h.slots 15 (by simp [searchSlots])).trans p.plan.attempt.tapeLength
  dsimp only [PPrimalityWords, SearchPublic.attempt, SearchPublic.attemptPlan,
    PPrimalityPlan.reframe, PConstructPlan.reframe, HashPlan.reframe]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [attemptWords, upd, h1, h3, h4, h5]
  · simpa [attemptWords, upd] using h14
  · simpa [attemptWords, upd] using h15

theorem searchEntry_ready {pLen qLen : Nat} (H : Spec.Mgf1.Hash) {p : SearchPublic} {s : State}
    (h : SearchBefore pLen qLen p s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.pAttemptArgs) s
      (PPrimalityBefore H pLen qLen p.attempt) := by
  obtain ⟨⟨W, hs, hu⟩, ctrl, ub, hp, hq⟩ := h
  have entry := hs.entry p.offset p.carry H
  have step := attemptEntry_ok entry ctrl.x0 (ctrl.scr.ld (d := 8) (by decide)) ctrl.offset
  refine WP.mono step fun t ⟨state, ff, hk⟩ => ?_
  have words := search_attempt_words (p := p) hs
  refine ⟨⟨attemptWords W p.offset, words, ?_, ?_⟩,
    ub, ?_, ?_, hp, hq⟩
  · exact state
  · simpa [SearchPublic.attempt, attemptWords, upd] using hu
  · exact source_of_frame hs.tape ff (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact p.plan.tapeSeparate _ (by
        change (⟨p.plan.attempt.construct.hash.F, frameBytes⟩ : Region) ∈ searchWrites p.plan.attempt p.plan.C
        simp [searchWrites])) p.plan.attempt.randMax hk.rd hk.wr
  · refine ⟨?_, by rw [hk.rd, hk.wr]; exact hs.tapeCover⟩
    simpa [SearchPublic.attempt, SearchPublic.attemptPlan, PPrimalityPlan.reframe, PConstructPlan.reframe,
      HashPlan.reframe, attemptWords, upd] using hs.arena.congr hk.wr

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PAttemptTailCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PConstructTestCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PPrimalityReadyCT`, which only this module used -/

section

/-! # Construction preserves the public primality inputs and entropy cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.Generation.Layout

theorem pPrimality_ready {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    {pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore H pLen qLen p s) :
    WP isa (Impl.Dsa.AArch64.Generation.pConstruct G pLen qLen) s (PPrimalityAfter p) := by
  obtain ⟨⟨W, hw, hs, hu⟩, hub, tape, ⟨arena, cover⟩, hp, hq⟩ := h
  let q := p.plan.withWords W hw
  have step := pConstruct_ok hG hmatch hsize
    (p := q.construct) (hd.trans hq.symm) hs
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hhash)
    (by simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords, hq] using hseedsize)
  change WP isa (Impl.Dsa.AArch64.Generation.pConstruct G p.plan.construct.len p.plan.construct.hash.len) s _ at step
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨bt, _, ho, hb, L, ⟨V, R⟩, ws, ptr, ff, rd, wr⟩ => ?_
  have bt' : Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p)
      p.plan.construct.len = Spec.Dsa.encodeBE p.plan.construct.len p.plan.construct.value := by
    simpa only [q, PPrimalityPlan.withWords, PConstructPlan.withWords, HashPlan.withWords,
      PConstructPlan.value, hw.1 5 (by decide)] using bt
  have sq := source_of_frame tape ff q.tapeConstruct p.plan.randMax rd wr
  refine ⟨L, ⟨V, W, R, hw, hu⟩, ws, ?_, bt', ho, hb, ?_, sq, arena.congr wr, by rw [rd, wr]; exact cover,
    hub⟩
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
      simp [Spec.Rsa.bytesAt, VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, hi']
    · intro i hi
      exact p.plan.construct.pOutside i (by simpa only [VG.Proof.Dsa.encodeBE_length] using hi)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.PPrimalityTestCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PPrimalityCallCT`, which only this module used -/

section

/-! # Instantiate the public width guard and primality call for a p candidate -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.Generation VG.Impl.Dsa.Generation.Layout

def PPrimalityPublic.width (p : PPrimalityPublic)
    (hb : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len)) : CandidateWidthPublic where
  B := p.plan.construct.B
  F := p.plan.construct.hash.F
  Z := p.plan.construct.Z
  w := p.plan.construct.len / 8
  ptr := VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p
  len := p.plan.construct.len
  value := p.plan.construct.value
  positive := by rcases p.plan.construct.width with h | h | h <;> omega_using [h]
  fits := by simpa only [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using hb

theorem pPrimality_width {p : PPrimalityPublic} {s : State} (h : PPrimalityAfter p s) :
    CandidateWidthBefore (p.width h.fits) s := by
  refine ⟨h.ws, h.layout.sp, h.pointer, h.bytes, ?_⟩
  have read := h.source.rd 0 (by
    rw [VG.Proof.Dsa.encodeBE_length]
    exact (p.width h.fits).positive)
  simpa only [PPrimalityPublic.width, VG.Proof.Bignum.off, BitVec.add_zero] using read

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
  have hc : Impl.Dsa.AArch64.ProbablePrime.candidate (8 * p.plan.construct.len) = Impl.Dsa.Generation.Layout.p := by
    change (if 8 * p.plan.construct.len ≤ 256 then _ else _) = _
    exact ite_eq_right (by rcases p.plan.construct.width with hh | hh | hh <;> omega_using [hh])
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
        (VG.Proof.Bignum.off (p.plan.construct.hash.W 5) Impl.Dsa.Generation.Layout.p) p.plan.construct.len) = _
      rw [h.bytes]
      exact VG.Proof.Dsa.decodeBE_encodeBE (p.width domain.upper).fits
    odd := h.odd
    bitLen := (p.plan.prime domain).bitLength_eq }⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Public width rejection and full-width primality form one native p test -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/PTestFullCT.lean`, which only this module imported.
section

/-! # Full-width candidates proceed to the probable-prime call -/

section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure PTestFullPublic (len : Nat) where
  width : CandidateWidthPublic
  call : PrimeTestPublic (8 * len)
  full : ¬ width.value < 2 ^ (8 * width.len - 1)

def PTestFullBefore (len : Nat) (p : PTestFullPublic len) (s : State) : Prop :=
  PrimeTestBefore (8 * len) p.call s ∧ CandidateWidthBefore p.width s

theorem pTestFull_ready {len : Nat} {p : PTestFullPublic len} {s : State}
    (h : PTestFullBefore len p s) : WP isa (.block candidateWidth) s fun t =>
      PrimeTestBefore (8 * len) p.call t ∧ eval (.zero .x .x3) t = some false := by
  refine WP.mono (candidateWidth_ok h.2.ws h.2.pointer p.width.positive p.width.fits h.2.bytes h.2.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  obtain ⟨W, V, hi⟩ := h.1
  exact ⟨⟨W, V, hi.congr hm hk.sp hk.rd hk.wr⟩, by simpa only [decide_eq_false p.full] using cf⟩

theorem pTest_full_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PTestFullBefore len)) (pTest T.run len) (fun _ _ => True) := by
  unfold pTest
  refine RelCT.seq (two_post ((two_map PTestFullPublic.width (fun _ _ h => h.2) candidateWidth_ct).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => pTestFull_ready h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · apply RelCT.of_false
    rintro s t ⟨p, hs, _, _⟩
    cases Option.some.inj (hs.1.2.symm.trans hs.2)
  · apply two_map PTestFullPublic.call (fun _ _ h => h.1.1)
    apply primeCall_ct T
    rcases hlen with rfl | rfl | rfl <;> unfold ProbablePrime.Supported <;> decide

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

def PPrimalityTestBefore (len : Nat) (p : PPrimalityPublic) (s : State) : Prop :=
  PPrimalityAfter p s ∧ p.plan.construct.len = len

theorem pPrimalityTest_ct (T : PrimeTest) (len : Nat)
    (hlen : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (PPrimalityTestBefore len)) (pTest T.run len) (fun _ _ => True) := by
  intro s t a b s' t' h es et
  obtain ⟨p, ⟨hs, he⟩, ⟨ht, _⟩, hsp⟩ := h
  by_cases small : p.plan.construct.value < 2 ^ (8 * p.plan.construct.len - 1)
  · exact pTest_small_ct T.run len s t a b s' t'
      ⟨p.width hs.fits, ⟨pPrimality_width hs, small⟩, ⟨pPrimality_width ht, small⟩, hsp⟩ es et
  · let domain : VG.Proof.Dsa.Generation.PDomain p.plan.construct.len p.plan.construct.value :=
      ⟨p.plan.construct.width, hs.odd, Nat.le_of_not_gt small, hs.fits⟩
    subst he
    let full : PTestFullPublic p.plan.construct.len := ⟨p.width hs.fits, p.primeCall domain, small⟩
    have state : ∀ u, PPrimalityAfter p u → PTestFullBefore p.plan.construct.len full u :=
      fun u hu => ⟨pPrimality_primeCall hu domain, pPrimality_width hu⟩
    exact pTest_full_ct T _ hlen s t a b s' t' ⟨full, state s hs, state t ht, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Complete candidate construction, width rejection and primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem pConstructTest_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore H pLen qLen))
      (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map PPrimalityPublic.construct (fun _ _ h => pPrimality_construct h)
    (pConstruct_ct hG H pLen qLen sizes hmatch hsize hhash hseedsize hd)) ?_)
    (pPrimalityTest_ct T pLen ?_)
  · intro p s h
    exact WP.mono (pPrimality_ready hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2.2.1⟩
  · rcases sizes with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Return the verified p-test result to the bounded search controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

def PPrimalityPublic.returnFrame (p : PPrimalityPublic) : AttemptReturnPublic :=
  ⟨p.plan.construct.hash.F, p.plan.construct.hash.S, p.plan.construct.hash.W 5⟩

theorem pAttemptTail_ready {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (T : PrimeTest) {pLen qLen : Nat} {H : Spec.Mgf1.Hash}
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) {p : PPrimalityPublic} {s : State}
    (h : PPrimalityBefore H pLen qLen p s) :
    WP isa (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) s (AttemptReturnBefore p.returnFrame) := by
  obtain ⟨⟨W, hw, hs, hu⟩, hub, tape, ⟨arena, cover⟩, hp, hq⟩ := h
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
    VG.Proof.RsaOaep.AArch64.upd, PPrimalityPublic.returnFrame,
    show ¬ (5 : Nat) = 19 by decide, show ¬ (5 : Nat) = 16 by decide, ite_false] using hw.1 5 (by decide)

theorem pAttemptTail_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PPrimalityBefore H pLen qLen))
      (.seq (.seq (pConstruct G pLen qLen) (pTest T.run pLen)) (.block searchReturn))
      (fun _ _ => True) :=
  RelCT.seq (two_post (pConstructTest_ct hG T H pLen qLen sizes hmatch hsize hhash hseedsize hd)
    (fun _ _ h => pAttemptTail_ready hG T hmatch hsize hhash hseedsize hd h))
    (two_map PPrimalityPublic.returnFrame (fun _ _ h => h) searchReturn_ct)

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # One complete native p-search iteration has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem searchBody_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore pLen qLen)) (pAttempt G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold pAttempt
  refine RelCT.seq (two_post (two_map SearchPublic.pointers (fun _ _ h => searchBefore_pointers h)
    pAttemptArgs_ct) (fun _ _ h => searchEntry_ready H h)) ?_
  exact two_map SearchPublic.attempt (fun _ _ h => h)
    (pAttemptTail_ct hG T H pLen qLen sizes hmatch hsize hhash hseedsize hd)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SearchIterationCTState`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchTailCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.SearchControlCT`, which this module and modules that import it used -/

section

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
          ite_eq_right (show ¬ limit ≤ p.counter + 1 by omega_using [he]), decide_eq_true he]; rfl
      · simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hf,
          ite_eq_left (show limit ≤ p.counter + 1 by omega_using [he]), decide_eq_false he]; rfl⟩

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

end

end

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

end

end

/-! ### `Dsa.AArch64.Generation.SearchTailReadyCT`, which only this module used -/

section

/-! # Controller-tail framing and the exact public continuation decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem searchTail_ready {limit stride : Nat} (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {p : SearchControlPublic} {s : State} (h : SearchAdvanceBefore limit stride p s) :
    WP isa (.seq (.block pSearchStatusCmp)
      (.seq (.ite (.zero .x .x3) (pSearchAdvance limit stride) (.block [])) (.block pSearchStatusCmp))) s fun t =>
      SearchControlCompared (p.next limit) t ∧ Outside p.B 0 24 s.mem t.mem ∧ Keep [.x3, .x4, .x5, .x7] s t := by
  refine WP.seq (WP.mono (searchStatusCmp_ok h.1.1 p.statusBound h.1.2)
    fun u ⟨uz, um, uk⟩ => ?_)
  have ctrl := h.1.1.congr um uk
  have before : SearchTailCompared limit stride p u := ⟨⟨⟨ctrl, um ▸ h.1.2⟩, h.2⟩, uz⟩
  by_cases retry : p.status = 3
  · refine WP.seq (WP.ite true (by simpa only [decide_eq_true retry] using uz) (fun _ => ?_) (fun he => Bool.noConfusion he))
    have ctrl' : SearchControl p.B p.counter stride u := by rw [← h.2.2]; exact ctrl
    refine WP.mono (searchAdvance_ok ctrl' h.2.1 hl hs) fun v ⟨vc, vs, vf, vk⟩ => ?_
    have next : SearchControlBefore (p.next limit) v := by
      simpa only [SearchControlBefore, SearchControlPublic.next, retry, ite_true, h.2.2] using And.intro vc vs
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, ?_⟩
    · simpa only [tm, um] using vf
    · exact ((uk.trans vk).trans tk).mono (by decide)
  · refine WP.seq (WP.ite false (by simpa only [decide_eq_false retry] using uz) (fun he => Bool.noConfusion he)
      (fun _ => WP.block_nil ?_))
    have next := searchTail_stop before (by simpa only [decide_eq_false retry] using uz)
    refine WP.mono (searchStatusCmp_ok next.1 (p.next limit).statusBound next.2)
      fun t ⟨tz, tm, tk⟩ => ?_
    refine ⟨⟨⟨next.1.congr tm tk, tm ▸ next.2⟩, tz⟩, ?_, (uk.trans tk).mono (by decide)⟩
    rw [tm, um]; exact Outside.refl _ _ _ _

end VG.Proof.Dsa.AArch64.Generation

end

end

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

end

end

/-! # Complete p-search iteration, including its public continuation decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation VG.Impl.Bignum.AArch64

theorem searchIteration_ct_of (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen)
    (hl : 32 * pLen ≤ 12288) (hs : (8 * pLen - 1) / (8 * qLen) + 1 ≤ 12)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (pSearchAdvanceHead (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))) hc).isSome = true) :
    RelCT isa (Two (SearchBefore pLen qLen))
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter pLen qLen)) := by
  unfold pSearchIteration
  simp only [seqs]
  have body : RelCT isa (Two (SearchBefore pLen qLen)) (pAttempt G1 G256 T.run pLen qLen)
      (Two (SearchBodySized pLen qLen)) := by
    refine two_post (searchBody_ct G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd) ?_
    intro p s h
    exact WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
      fun _ ht => ⟨ht, h.2.2.2⟩
  refine RelCT.seq body (two_post ((two_map SearchPublic.control (fun _ _ h => searchBody_control h)
    (searchTail_ct (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1) hl hs ht)).mono
    (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => searchIteration_tail h hl hs))

theorem searchIteration_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchBefore pLen qLen))
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two (SearchIterationAfter pLen qLen)) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact searchIteration_ct_of G1 G256 T H _ _ (by unfold GenerationSizes; decide)
      hG hmatch hsize hhash hseedsize hd (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SearchInitCT`, which only this module used -/

section

/-! # Initialize the bounded p search without assumptions about old controller words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

def SearchStart (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  (∃ W, SearchMemory p.plan W s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    Scr s p.plan.C 24 ∧
    p.used ≤ p.plan.attempt.rand.length ∧ p.plan.attempt.construct.len = pLen ∧
    p.plan.attempt.construct.hash.len = qLen ∧ p.counter = 0

def SearchInitBefore (pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  SearchStart pLen qLen p s ∧ s.gpr .x0 = p.plan.C

def SearchPublic.returnFrame (p : SearchPublic) : AttemptReturnPublic :=
  ⟨p.plan.attempt.construct.hash.F, p.plan.attempt.construct.hash.S, p.plan.attempt.construct.hash.W 5⟩

theorem searchStart_frame {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchStart pLen qLen p s) : AttemptReturnBefore p.returnFrame s := by
  obtain ⟨W, memory, _⟩ := h.1
  obtain ⟨V, R⟩ := memory.rep
  exact ⟨memory.layout, V, W, R, memory.slots 5 (by simp [searchSlots])⟩

theorem searchBase_ready {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchStart pLen qLen p s) :
    WP isa (.block controlBase) s (SearchInitBefore pLen qLen p) := by
  obtain ⟨⟨W, memory, used⟩, scr, bound, hp, hq, counter⟩ := h
  obtain ⟨V, R⟩ := memory.rep
  have base : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = p.plan.C := by
    rw [memory.slots 5 (by simp [searchSlots])]; exact p.plan.controlBase
  refine WP.mono (controlBase_ok memory.layout R base) fun t ⟨hdi, hm, hk⟩ => ?_
  have L := memory.layout.congr hk.sp hk.wr (by rw [hm])
  have mt := memory.frame L ⟨V, hm ▸ R⟩ (fun _ _ => rfl)
    (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr
  exact ⟨⟨⟨W, mt, used⟩, scr.congr hk.wr, bound, hp, hq, counter⟩, hdi⟩

theorem searchInit_ready {pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchInitBefore pLen qLen p s) :
    WP isa (.block pSearchInit) s (SearchBefore pLen qLen p) := by
  obtain ⟨⟨⟨W, memory, used⟩, scr, bound, hp, hq, counter⟩, hdi⟩ := h
  refine WP.mono (searchInit_ok scr hdi (p.plan.attempt.construct.hash.count + 1))
    fun t ⟨ctrl, ff, hk⟩ => ?_
  have mt := SearchMemory.stable memory (ff.mono (by decide) (by decide)) (hk.mono (by decide))
  exact ⟨⟨W, mt, used⟩, (by rw [counter]; exact ctrl), bound, hp, hq⟩

theorem searchInit_ct (pLen qLen : Nat) :
    RelCT isa (Two (SearchInitBefore pLen qLen)) (.block pSearchInit) (Two (SearchBefore pLen qLen)) := by
  refine two_post (two_taint [.x0] ?_ (by taint_decide)) (fun _ _ h => searchInit_ready h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr; subst r
  exact hs.2.trans ht.2.symm

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SeedPrimeCT`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.Generation.SeedSearchStateCT`, which only this module used -/

section

/-! # Instantiate the public prime-search state from actual persistent-frame words -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem seedPrime_memory {p : SeedPublic} {s : State} {W : Nat → BitVec 64}
    (hm : GenerationMemory p.context W s) (seed : GenerationTapeMemory p.seed s)
    (h1 : W 1 = p.seed.ptr) (h10 : W 10 = p.seedCursor)
    (hq : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.context.geo.B q) p.context.geo.qLen =
      Spec.Dsa.encodeBE p.context.geo.qLen (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)) :
    SearchMemory p.searchPlan W s := by
  have state := hm.searchState p.seed p.length seed h1 hq
  have h5 : W 5 = p.context.saved 5 := hm.slots 5 (by simp [generationSlots])
  refine {
    layout := state.layout
    rep := state.rep
    slots := seedPrime_words hm h1 h10
    label := state.label.congr rfl rfl rfl ?_
    seedRead := state.seedRead
    wrappedWrite := state.wrappedWrite
    hashWrite := state.hashWrite
    seed := state.seed
    scratch := state.scratch
    qSource := ?_
    tape := state.tape
    shapedWrite := ?_
    pWrite := ?_
    exponentWrite := ?_
    witnessWrite := ?_
    arena := ?_
    tapeCover := state.tapeCover }
  · change p.context.saved 26 = W 26
    exact (hm.slots 26 (by simp [generationSlots])).symm
  · have src := state.qSource
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (W 5) q) _ at src
    change Src s (VG.Proof.Bignum.off p.context.geo.B arithmetic) arithmeticBytes (VG.Proof.Bignum.off (p.context.saved 5) q) _
    rw [h5] at src
    exact src
  · have write := state.shapedWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) shaped) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) shaped) i) 1
    rw [h5] at write
    exact write
  · have write := state.pWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) VG.Impl.Dsa.Generation.Layout.p) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) VG.Impl.Dsa.Generation.Layout.p) i) 1
    rw [h5] at write
    exact write
  · have write := state.exponentWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) exponent) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) exponent) i) 1
    rw [h5] at write
    exact write
  · have write := state.witnessWrite
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) witness) i) 1 at write
    change ∀ i < p.context.geo.pLen, InRegions s.wr (VG.Proof.Bignum.off (VG.Proof.Bignum.off (p.context.saved 5) witness) i) 1
    rw [h5] at write
    exact write
  · have a := state.arena
    change Scr s (W 5) domainCheck at a
    change Scr s (p.context.saved 5) domainCheck
    rw [h5] at a
    exact a

theorem seedPrime_start {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) : SearchStart pLen qLen p.search s := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, heQ⟩, heP, hq⟩ := h
  exact ⟨⟨W, seedPrime_memory hm seed h1 h10 hq, h16⟩,
    hm.scratch.sub (p.context.geo.small_bound (d := control) (n := 24) (by decide) (by decide)) (by decide),
    p.bound, heP, heQ, rfl⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.NativeSearchCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.PSearchLoopCT`, which only this module used -/

section

/-! # Timing of the bounded native p search, including its exact retry cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation VG.Impl.Bignum.AArch64

private def searchLoopInv (pLen qLen remaining : Nat) : State → State → Prop :=
  Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchBefore pLen qLen p s

section
variable (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
variable (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
variable (sizes : GenerationSizes pLen qLen)
variable (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
variable (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
variable (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
variable (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
variable (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
variable (hd : (if qLen = 20 then G1 else G256).D = qLen)

include hG hmatch hsize hhash hseedsize hd sizes

theorem searchIteration_ready {p : SearchPublic} {s : State} (h : SearchBefore pLen qLen p s) :
    WP isa (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) s (SearchIterationAfter pLen qLen p) := by
  unfold pSearchIteration
  simp only [seqs]
  refine WP.seq (WP.mono (searchBody_ready G1 G256 T hG hmatch hsize hhash hseedsize hd h)
    fun _ ht => searchIteration_tail ⟨ht, h.2.2.2⟩ ?_ ?_)
  all_goals rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem searchLoop_step (remaining : Nat) :
    RelCT isa (searchLoopInv pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (fun s t => isa.eval (.zero .x .x3) s = isa.eval (.zero .x .x3) t ∧ (isa.eval (.zero .x .x3) s = some false → True) ∧
        (isa.eval (.zero .x .x3) s = some true → ∃ next < remaining, searchLoopInv pLen qLen next s t)) := by
  have step : RelCT isa (searchLoopInv pLen qLen remaining)
      (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
        (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1))
      (Two fun p s => 32 * pLen - p.counter = remaining ∧ SearchIterationAfter pLen qLen p s) := by
    refine two_post ((searchIteration_ct G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (searchIteration_ready G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd h.2)
      fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have next := hs.2 cont
  have bound : p.counter + 1 < 32 * pLen := by
    have hb := (of_decide_eq_true cont).2
    rw [show p.plan.attempt.construct.len = pLen from next.2.2.2.1] at hb
    exact hb
  refine ⟨32 * pLen - (p.counter + 1), by omega_using [hr, bound], p.next cont, ⟨rfl, next⟩, ⟨rfl, ht.2 cont⟩, hsp⟩

theorem pSearchLoop_ct : RelCT isa (Two (SearchBefore pLen qLen))
    (.loop (pSearchIteration (pAttempt G1 G256 T.run pLen qLen)
      (32 * pLen) ((8 * pLen - 1) / (8 * qLen) + 1)) (.zero .x .x3)) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht, hsp⟩ es et
  exact RelCT.loop (searchLoopInv pLen qLen)
    (searchLoop_step G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd)
    (32 * pLen - p.counter) s t a b s' t' ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end
end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The complete bounded native p search has a public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem primeSearch_ct (G1 G256 : Impl.Pbkdf2.Md.AArch64.Hash)
    (T : PrimeTest) (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hG : Calls.StreamOK (if qLen = 20 then G1 else G256).stream)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x)
    (hsize : ∀ x, (H.hash x).length = (if qLen = 20 then G1 else G256).D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : (if qLen = 20 then G1 else G256).D = qLen) :
    RelCT isa (Two (SearchStart pLen qLen)) (primeSearch G1 G256 T.run pLen qLen)
      (fun _ _ => True) := by
  unfold primeSearch pSearch
  refine RelCT.seq (two_post ((two_map SearchPublic.returnFrame (fun _ _ h => searchStart_frame h)
    controlBase_ct).mono (fun _ _ h => h) (fun _ _ _ => True.intro))
    (fun _ _ h => searchBase_ready h)) (RelCT.seq (searchInit_ct pLen qLen) ?_)
  exact pSearchLoop_ct G1 G256 T H pLen qLen sizes hG hmatch hsize hhash hseedsize hd

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The accepted subgroup enters the complete public-trace prime search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64

theorem seedPrime_ct (H : GenerationHashes) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) (fun _ _ => True) := by
  have hq : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  exact two_map SeedPublic.search (fun _ _ h => seedPrime_start h)
    (primeSearch_ct H.sha1 H.sha256 T (generationHash qLen) pLen qLen sizes
      (H.streamOK qLen) (H.hash_matches qLen) (H.hash_size qLen)
      (generationHash_seed hq) (H.seed_size hq) (H.hash_width hq))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Status inspection preserves the seed phase inputs -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SeedSubgroupResultCT.lean`, which only this module imported.
section

/-! # Subgroup outcomes determine the public phase status and entropy cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def SeedPublic.subgroupResult (p : SeedPublic) : Option (Bool × List Byte) :=
  Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes)
    (p.context.rand.bytes.drop p.used)

def SeedPublic.subgroupStatus (p : SeedPublic) : BitVec 64 :=
  match p.subgroupResult with
  | none => 0
  | some (b, _) => if b then 1 else 3

def SeedPublic.afterSubgroup (p : SeedPublic) : SeedPublic :=
  { p with
    used := match p.subgroupResult with
      | none => p.used
      | some (_, rest) => p.context.rand.bytes.length - rest.length
    bound := by cases p.subgroupResult with
      | none => exact p.bound
      | some res => exact Nat.sub_le _ _ }

def SeedSubgroupAfter (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.subgroupStatus) ∧
  (p.subgroupStatus = 1 → SeedPrimeBefore pLen qLen p.afterSubgroup s)

theorem seedSubgroup_after (H : GenerationHashes) (T : PrimeTest)
    {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedBefore qLen p s) (hp : p.context.geo.pLen = pLen) :
    WP isa (.seq (.block (Impl.Dsa.AArch64.Generation.seedArguments qLen))
      (Impl.Dsa.AArch64.Generation.subgroup H.sha1 H.sha256 T.run qLen)) s
      (SeedSubgroupAfter pLen qLen p) := by
  obtain ⟨⟨W, hm, h1, h16, h10⟩, seed, he⟩ := h
  have step := seedSubgroup_ok H T hm p.seed p.length seed h1 h16 p.bound
  subst qLen
  refine WP.mono step fun t ⟨used', status, bound, ht, bytes, fail, result, ff, rd, wr⟩ => ?_
  have statusEq : status = p.subgroupStatus := by
    cases hr : p.subgroupResult with
    | none => simpa [SeedPublic.subgroupStatus, hr] using fail hr
    | some res =>
      obtain ⟨b, rest⟩ := res
      have hs := (result b rest hr).1
      cases b <;> simpa [SeedPublic.subgroupStatus, hr] using hs
  refine ⟨⟨_, ht, by simpa [upd] using statusEq⟩, ?_⟩
  intro accepted
  have cursor : used' = p.afterSubgroup.used := by
    cases hr : p.subgroupResult with
    | none => simp [SeedPublic.subgroupStatus, hr] at accepted
    | some res =>
      obtain ⟨b, rest⟩ := res
      simpa [SeedPublic.afterSubgroup, hr] using (result b rest hr).2
  refine ⟨⟨⟨_, ht, ?_, ?_, ?_⟩, seed.frame ff rd wr, rfl⟩, hp, bytes⟩
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h1
  · simp [upd, cursor]
  · simpa [seedWords, upd, SeedPublic.afterSubgroup] using h10

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Proof.MlKem.AArch64

theorem seedBefore_congr {qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedBefore qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedBefore qLen p t := by
  obtain ⟨⟨W, hW, h1, h16, h10⟩, seed, he⟩ := h
  exact ⟨⟨W, hW.congr hm hk, h1, h16, h10⟩,
    seed.frame (by rw [hm]; exact Frame.refl _ _) hk.rd hk.wr,
    he⟩

theorem seedPrimeBefore_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeBefore pLen qLen p t :=
  ⟨seedBefore_congr h.1 hm hk, h.2.1, hm ▸ h.2.2⟩

theorem seedSubgroupAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedSubgroupAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedSubgroupAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  exact ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => seedPrimeBefore_congr (next ha) hm hk⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.GeneratorCallCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.SeedGeneratorPlanCT`, which this module and modules that import it used -/

section

/-! # Public accepted primes determine the generator-search plan -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGeneratorWork.lean`, which only this module imported.
section

/-! # Geometry of the generator's parent and arithmetic workspaces -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeometryGenerator.lean`, which only this module imported.
section

/-! # Concrete generator plan over the saved p and exponent buffers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/ContextGenerator.lean`, which only this module imported.
section

/-! # Saved p and exponent bytes supply the complete generator search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure SeedGeneratorPublic where
  seed : SeedPublic
  value : Nat
  domain : VG.Proof.Dsa.Generation.PDomain seed.context.geo.pLen value

def SeedGeneratorPublic.qValue (p : SeedGeneratorPublic) : Nat :=
  Spec.Dsa.qCandidate (8 * p.seed.context.geo.qLen) p.seed.seed.bytes

def SeedGeneratorBefore (pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  SeedPrimeBefore pLen qLen p.seed s ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value ∧
  Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.seed.context.geo.B exponent) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Calling the generator stage in constant time

The stage's arguments are the generation's pointers and lengths, and its
leak, p, q and the h tape, is public. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout

theorem SeedGeneratorPublic.q_bounds (a : SeedGeneratorPublic) :
    0 < a.qValue ∧ a.qValue < 256 ^ a.seed.context.geo.qLen := by
  have shape := VG.Proof.Dsa.Generation.qCandidate_shape
    (by rcases a.seed.context.geo.qWidth with hh | hh <;> omega_using [hh] : 2 ≤ 8 * a.seed.context.geo.qLen) a.seed.seed.bytes
  refine ⟨Nat.lt_of_lt_of_le (Nat.two_pow_pos _) shape.2.1, ?_⟩
  have := shape.2.2
  rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul]
  exact this

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SeedSubgroupCT`, which only this module used -/

section

/-! # Compose seed argument setup with the complete subgroup-generation phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem seedArguments_ct (qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore qLen)) (.block (seedArguments qLen)) (Two (SeedPrepared qLen)) := by
  rcases hlen with rfl | rfl
  all_goals
    exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
      (fun _ _ h => seedArguments_ready h)

theorem seedSubgroup_ct (H : GenerationHashes) (T : PrimeTest)
    (qLen : Nat) (hlen : qLen = 20 ∨ qLen = 32) :
    RelCT isa (Two (SeedBefore qLen))
      (.seq (.block (seedArguments qLen)) (subgroup H.sha1 H.sha256 T.run qLen)) (fun _ _ => True) :=
  RelCT.seq (seedArguments_ct qLen hlen)
    (two_map SeedPublic.subgroup (fun _ _ h => seedPrepared_subgroup h) (subgroup_ct H T qLen hlen))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.SeedPrimeFinishCT`, which only this module used -/

section

/-! # Prime search composes with generator selection and final domain checking -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/SeedPrimeResultCT.lean`, which only this module imported.
section

/-! # Public prime-search outcomes select the next generator phase -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64

def SeedPublic.primeResult (p : SeedPublic) : Option (Option Nat × List Byte) :=
  Spec.Dsa.primeFromSeed (8 * p.context.geo.pLen) (8 * p.context.geo.qLen)
    (Spec.Dsa.qCandidate (8 * p.context.geo.qLen) p.seed.bytes) p.seed.bytes (p.context.rand.bytes.drop p.used)

def SeedPublic.primeStatus (p : SeedPublic) : BitVec 64 :=
  match p.primeResult with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def SeedPublic.generatorPublic (p : SeedPublic) (value : Nat) (rest : List Byte)
    (domain : VG.Proof.Dsa.Generation.PDomain p.context.geo.pLen value) : SeedGeneratorPublic :=
  ⟨{ p with used := p.context.rand.bytes.length - rest.length, bound := Nat.sub_le _ _ }, value, domain⟩

def SeedPrimeAfter (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  (∃ W, GenerationMemory p.context W s ∧ W 19 = p.primeStatus) ∧
  (p.primeStatus = 1 → ∃ value rest, p.primeResult = some (some value, rest) ∧
    ∃ domain, SeedGeneratorBefore pLen qLen (p.generatorPublic value rest domain) s)

theorem seedPrime_after (H : GenerationHashes) (T : PrimeTest)
    {pLen qLen : Nat} {p : SeedPublic} {s : State}
    (h : SeedPrimeBefore pLen qLen p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen) s
      (SeedPrimeAfter pLen qLen p) := by
  obtain ⟨⟨⟨W, hm, h1, h16, h10⟩, seed, hq⟩, hp, bq⟩ := h
  subst pLen; subst qLen
  refine WP.mono (seedPrime_ok H T hm p.seed p.length seed h1 bq h16 p.bound)
    fun t ⟨Wt, used, bound, ht, u16, slots, bq', outcome, ff, rd, wr⟩ => ?_
  rcases outcome with ⟨hs, hr⟩ | ⟨hs, value, hr, domain, bp, be⟩ | ⟨hs, hr⟩
  · have status : p.primeStatus = 0 := by simp [SeedPublic.primeStatus, SeedPublic.primeResult, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩
  · have result : p.primeResult = some (some value, p.context.rand.bytes.drop used) := hr
    have status : p.primeStatus = 1 := by simp [SeedPublic.primeStatus, result]
    refine ⟨⟨Wt, ht, hs.trans status.symm⟩, fun _ =>
      ⟨value, p.context.rand.bytes.drop used, result, domain, ?_⟩⟩
    refine ⟨⟨⟨⟨Wt, ht, ?_, ?_, ?_⟩, seed.frame ff rd wr,
      rfl⟩, rfl, bq'⟩, bp, be⟩
    · exact (slots 1 (by simp [searchSlots])).trans h1
    · change Wt 16 = BitVec.ofNat 64 (p.context.rand.bytes.length - (p.context.rand.bytes.drop used).length)
      rw [List.length_drop, Nat.sub_sub_self bound]
      exact u16
    · exact (slots 10 (by simp [searchSlots])).trans h10
  · have status : p.primeStatus = 3 := by simp [SeedPublic.primeStatus, SeedPublic.primeResult, hr]
    exact ⟨⟨Wt, ht, hs.trans status.symm⟩, by simp [status]⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem seedGeneratorBefore_congr {pLen qLen : Nat} {p : SeedGeneratorPublic} {s t : State}
    (h : SeedGeneratorBefore pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedGeneratorBefore pLen qLen p t :=
  ⟨seedPrimeBefore_congr h.1 hm hk, hm ▸ h.2.1, hm ▸ h.2.2⟩

theorem seedPrimeAfter_congr {pLen qLen : Nat} {p : SeedPublic} {s t : State}
    (h : SeedPrimeAfter pLen qLen p s) (hm : t.mem = s.mem) (hk : Keep [.x3, .x4] s t) :
    SeedPrimeAfter pLen qLen p t := by
  obtain ⟨⟨W, hW, hs⟩, next⟩ := h
  refine ⟨⟨W, hW.congr hm hk, hs⟩, fun ha => ?_⟩
  obtain ⟨value, rest, hr, domain, ht⟩ := next ha
  exact ⟨value, rest, hr, domain, seedGeneratorBefore_congr ht hm hk⟩

theorem seedPrimeAfter_related {pLen qLen : Nat} {s t : State}
    (h : Two (fun p s => SeedPrimeAfter pLen qLen p s ∧ p.primeStatus = 1) s t) :
    Two (SeedGeneratorBefore pLen qLen) s t := by
  obtain ⟨p, hs, ht, hsp⟩ := h
  obtain ⟨vs, rs, hrs, ds, hgs⟩ := hs.1.2 hs.2
  obtain ⟨vt, rt, hrt, dt, hgt⟩ := ht.1.2 ht.2
  have eqs := Option.some.inj (hrs.symm.trans hrt)
  have hv := Option.some.inj (congrArg Prod.fst eqs)
  have hr : rs = rt := congrArg Prod.snd eqs
  subst vt; subst rt
  exact ⟨p.generatorPublic vs rs ds, hgs, hgt, hsp⟩

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # Timing of one seed of the refillable-tape search on AArch64

The seed's subgroup and prime search are the finite search's
(`SeedSubgroupCT.lean`, `SeedPrimeCT.lean`). After `p`, the generator stage
reads its `h` candidates from the window of `rand` after the octets
consumed, a function of public data (`StagePublic`); the stage's leak is
public as for the finite search, and its result, which the seed's status
branches on, a function of its public inputs. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

/-! ## The generator stage -/

/-- The generator stage's public inputs: its context, whose `h` tape is the
window, `p`, `q` and the octets of `rand` consumed before it. -/
structure StagePublic where
  ctx : GenerationContext
  value : Nat
  qval : Nat
  used : Nat
  domain : VG.Proof.Dsa.Generation.PDomain ctx.geo.pLen value
  qfit : qval < 256 ^ ctx.geo.qLen
  qpos : 0 < qval
  short : ctx.hs.bytes.length ≤ 128 * ctx.geo.pLen

def StagePublic.cands (a : StagePublic) : List Nat :=
  (Spec.Dsa.generationChunks a.ctx.geo.pLen a.ctx.hs.bytes).map Spec.Dsa.decodeBE

def StagePublic.code (a : StagePublic) : Nat := Proof.Dsa.GeneratorStage.code a.value a.qval a.cands

def StagePublic.count (a : StagePublic) : Nat :=
  a.ctx.geo.pLen * VG.Proof.Dsa.Generation.generatorCount a.value a.qval a.cands

theorem StagePublic.count_lt (a : StagePublic) : a.count < 2 ^ 32 := by
  have pn : a.ctx.geo.pLen ≤ 384 := by rcases a.ctx.geo.width with hh | hh | hh <;> omega_using [hh]
  have hc : VG.Proof.Dsa.Generation.generatorCount a.value a.qval a.cands ≤ a.ctx.hs.bytes.length / a.ctx.geo.pLen := by
    refine Nat.le_trans (VG.Proof.Dsa.Generation.generatorCount_le _ _ _) (Nat.le_of_eq ?_)
    simp only [StagePublic.cands, Spec.Dsa.generationChunks, List.length_map, List.length_range]
  have hm := Nat.mul_le_mul_left a.ctx.geo.pLen hc
  have hd : a.ctx.geo.pLen * (a.ctx.hs.bytes.length / a.ctx.geo.pLen) ≤ a.ctx.hs.bytes.length := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  have := a.short
  unfold StagePublic.count
  omega_using [pn, hm, hd, this]

/-- The stage's inputs in memory. -/
def StageInputs (a : StagePublic) (s : State) : Prop :=
  ∃ W, GenerationMemory a.ctx W s ∧ W 16 = BitVec.ofNat 64 a.used ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B VG.Impl.Dsa.Generation.Layout.p) a.ctx.geo.pLen =
      Spec.Dsa.encodeBE a.ctx.geo.pLen a.value ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B exponent) a.ctx.geo.pLen =
      Spec.Dsa.encodeBE a.ctx.geo.pLen ((a.value - 1) / a.qval) ∧
    Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off a.ctx.geo.B q) a.ctx.geo.qLen = Spec.Dsa.encodeBE a.ctx.geo.qLen a.qval

def StageBefore (pLen : Nat) (a : StagePublic) (s : State) : Prop :=
  a.ctx.geo.pLen = pLen ∧ StageInputs a s

/-- The stage's arguments in their registers. -/
def StageArgs (pLen : Nat) (a : StagePublic) (u : State) : Prop :=
  a.ctx.geo.pLen = pLen ∧ ∃ s, StageInputs a s ∧ u.gpr .x0 = a.ctx.geo.B ∧
    u.gpr .x1 = BitVec.ofNat 64 (usedBytes a.ctx.geo.pLen / 8) ∧
    u.gpr .x2 = a.ctx.hs.ptr ∧ u.gpr .x3 = BitVec.ofNat 64 a.ctx.hs.bytes.length ∧
    u.mem = s.mem ∧ u.sp = a.ctx.geo.F ∧ u.rd = s.rd ∧ u.wr = s.wr

/-- After the stage: its result in `x0`. -/
def StageCalled (a : StagePublic) (t : State) : Prop :=
  ∃ V W, Lay t a.ctx.geo.F a.ctx.geo.hash ∧ Rep t.mem a.ctx.geo.F a.ctx.geo.hash V W ∧
    W 16 = BitVec.ofNat 64 a.used ∧ W 13 = BitVec.ofNat 64 a.ctx.hs.bytes.length ∧
    t.gpr .x0 = BitVec.ofNat 64 (a.code + 4 * a.count)

theorem stageArgs_ct (pLen : Nat) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) hc).isSome = true) :
    RelCT isa (Two (StageBefore pLen)) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen))
      (Two (StageArgs pLen)) := by
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) ht fun a s ⟨hp, W, hm, h16, bp, be, bq⟩ => ?_
  subst hp
  exact WP.mono (generatorCallArgs_ok hm) fun u ⟨h0, h1, h2, h3, hmem, ku⟩ =>
    ⟨rfl, s, ⟨W, hm, h16, bp, be, bq⟩, h0, h1, h2, h3, hmem, ku.sp.trans hm.layout.sp, ku.rd, ku.wr⟩

theorem stageCall_ct (G : GeneratorStage) (pLen : Nat) (hb : Generator.Supported pLen) :
    RelCT isa (Two (StageArgs pLen)) (G.run pLen) (Two StageCalled) := by
  refine two_post ?_ fun a u h => ?_
  · refine RelCT.callExDit (G.verified pLen hb).1 (G.verified pLen hb).2.1 (G.noDit pLen hb) (fun _ _ h => h)
      fun u₁ u₂ ⟨a, h₁, h₂, _⟩ => ?_
    obtain ⟨hp, s₁, ⟨W₁, m₁, _, bp₁, be₁, bq₁⟩, h0₁, h1₁, h2₁, h3₁, hm₁, hsp₁, hr₁, hw₁⟩ := h₁
    obtain ⟨_, s₂, ⟨W₂, m₂, _, bp₂, be₂, bq₂⟩, h0₂, h1₂, h2₂, h3₂, hm₂, hsp₂, hr₂, hw₂⟩ := h₂
    have E₁ := generatorCall_entry m₁ a.value a.qval a.domain a.qfit a.qpos bp₁ be₁ bq₁ h0₁ h1₁ h2₁ h3₁ hm₁ hsp₁
      hr₁ hw₁
    have E₂ := generatorCall_entry m₂ a.value a.qval a.domain a.qfit a.qpos bp₂ be₂ bq₂ h0₂ h1₂ h2₂ h3₂ hm₂ hsp₂
      hr₂ hw₂
    subst hp
    refine ⟨_, _, _, _, E₁.pre, E₂.pre, ?_, E₁.reads, E₁.writes, E₂.reads, E₂.writes⟩
    sig_pub [Generator.contract, Proof.Dsa.GeneratorStage.contract, Proof.Dsa.GeneratorStage.sig, abi, argRegs]
    rw [hsp₁, hsp₂, h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂]
    have hl : (BitVec.ofNat 64 a.ctx.hs.bytes.length).toNat = a.ctx.hs.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.ctx.hs.size]
    rw [hl, E₁.pv, E₂.pv, E₁.qv, E₂.qv, E₁.tape, E₂.tape]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hp, s, ⟨W, hm, h16, bp, be, bq⟩, h0, h1, h2, h3, hmem, hsp, hrd, hwr⟩ := h
    subst hp
    refine WP.mono (generatorCall_call_ok G hm a.value a.qval a.domain a.qfit a.qpos bp be bq h0 h1 h2 h3 hmem hsp
      hrd hwr) fun t C => ?_
    obtain ⟨V, Lt, Rt, -, -, -⟩ := generatorCalled_memory hm C hwr hrd
    exact ⟨V, W, Lt, Rt, h16, (hm.slots 13 (by decide)).trans a.ctx.hLengthSlot, C.status⟩

theorem stageStatus_ct (pLen : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) hc₁).isSome =
      true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) hc₂).isSome = true) :
    RelCT isa (Two StageCalled) (Impl.Dsa.AArch64.Generation.Refill.stageStatus pLen) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.stageStatus
  refine RelCT.seq (two_piece (Ψ := fun a t => t.gpr .x4 = BitVec.ofNat 64 a.code - 3) [.x0] ?_ (by taint_decide)
    ?_) (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₁)
      (two_taint [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₂))
  · intro a s t ⟨_, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, ht⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.trans ht.symm
  · intro a s ⟨V, W, L, R, h16, _, hx⟩
    have hc : a.code < 4 := by
      rcases stage_code_cases a.value a.qval a.cands with h | h | h <;> simp only [StagePublic.code, h] <;> decide
    exact WP.mono (consumed_run L R hc a.count_lt hx h16) fun t ⟨⟨_, _, h4⟩, _⟩ => h4
  · intro a s t hs ht
    simp only [eval, State.read, hs, ht]

/-- The window, the stage and its status. -/
theorem refillGenerator_ct_of (G : GeneratorStage) (pLen : Nat) (hb : Generator.Supported pLen)
    {hc₀ hc₁ hc₂ hc₃ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₀ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) hc₀).isSome = true)
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.generatorCallArgs pLen)) hc₁).isSome =
      true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.shortStatus pLen)) hc₂).isSome =
      true)
    (ht₃ : (taint.check (Taint.ofRegs []) (.block Impl.Dsa.AArch64.Generation.Refill.foundStatus) hc₃).isSome = true)
    {α : Type} {Φ : α → State → Prop} (stage : α → StagePublic)
    (window : ∀ a s, Φ a s → WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s
      (StageBefore pLen (stage a))) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen) (fun _ _ => True) := by
  simp only [Impl.Dsa.AArch64.Generation.Refill.refillGenerator, VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_map stage (Φ' := fun b s => ∃ a, stage a = b ∧ Φ a s) (fun a s h => ⟨a, rfl, h⟩) ?_)
    (RelCT.seq (stageArgs_ct pLen ht₁) (RelCT.seq (stageCall_ct G pLen hb) (stageStatus_ct pLen ht₂ ht₃)))
  refine two_piece [] (fun _ _ _ _ _ _ hr => nomatch hr) ht₀ fun b s ⟨a, e, h⟩ => ?_
  subst e
  exact window a s h

/-! ## The window -/

/-- The window of `rand` after the octets `p`'s search consumed. -/
def SeedGeneratorPublic.window (a : SeedGeneratorPublic) : GenerationTape a.seed.context.geo :=
  a.seed.context.rand.slice a.seed.used (min (a.seed.context.rand.bytes.length - a.seed.used) (128 * a.seed.context.geo.pLen))
    (by have := a.seed.bound; omega_using [this])

def SeedGeneratorPublic.stage (a : SeedGeneratorPublic) : StagePublic where
  ctx := a.seed.context.withHs a.window
  value := a.value
  qval := a.qValue
  used := a.seed.used
  domain := a.domain
  qfit := a.q_bounds.2
  qpos := a.q_bounds.1
  short := by
    show (a.window).bytes.length ≤ 128 * a.seed.context.geo.pLen
    rw [SeedGeneratorPublic.window, slice_length]
    omega_using []

theorem seedGenerator_window {pLen qLen : Nat} {a : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore pLen qLen a s) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.window pLen)) s (StageBefore pLen a.stage) := by
  obtain ⟨⟨⟨⟨W, hm, _, h16, _⟩, _, _⟩, hp, bq⟩, bp, be⟩ := h
  subst hp
  have pn : a.seed.context.geo.pLen ≤ 384 := by rcases a.seed.context.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : a.seed.context.geo.qLen ≤ 32 := by rcases a.seed.context.geo.qWidth with hh | hh <;> omega_using [hh]
  have hp_b : VG.Impl.Dsa.Generation.Layout.p + a.seed.context.geo.pLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have he_b : exponent + a.seed.context.geo.pLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn])
  have hq_b : q + a.seed.context.geo.qLen ≤ usedBytes a.seed.context.geo.pLen :=
    a.seed.context.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [qn])
  refine WP.mono (refillWindow_ok hm h16 a.seed.bound rfl) fun t ⟨mt, ft, _, _⟩ => ⟨rfl, _, mt, ?_,
    (a.seed.context.geo.frame_bytes ft hp_b).trans bp, (a.seed.context.geo.frame_bytes ft he_b).trans be,
    (a.seed.context.geo.frame_bytes ft hq_b).trans bq⟩
  show upd (upd W 11 _) 13 _ 16 = BitVec.ofNat 64 a.seed.used
  simp [upd, h16]

theorem refillGenerator_ct (G : GeneratorStage) (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedGeneratorBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen) (fun _ _ => True) := by
  have hb : Generator.Supported pLen := by rcases sizes with h | h | h <;> simp [h.1, Generator.Supported]
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact refillGenerator_ct_of G _ hb (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
      SeedGeneratorPublic.stage fun _ _ h => seedGenerator_window h

/-! ## The seed -/

theorem refillPrimeFinish_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (SeedPrimeBefore pLen qLen))
      (.seq (Impl.Dsa.AArch64.Generation.primeSearch H.sha1 H.sha256 T.run pLen qLen)
        (Impl.Dsa.AArch64.Generation.onSuccess (Impl.Dsa.AArch64.Generation.Refill.refillGenerator G.run pLen)))
      (fun _ _ => True) := by
  refine RelCT.seq (two_post (seedPrime_ct H T pLen qLen sizes)
    (fun _ _ h => seedPrime_after H T h)) ?_
  apply onSuccess_ct (Φ := SeedPrimeAfter pLen qLen) SeedPublic.context SeedPublic.primeStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedPrimeAfter_congr h hm hk)
  exact (refillGenerator_ct G pLen qLen sizes).mono
    (fun _ _ h => seedPrimeAfter_related h) (fun _ _ h => h)

/-- A seed's attempt from its public inputs. -/
def RefillAttemptBefore (pLen qLen : Nat) (p : SeedPublic) (s : State) : Prop :=
  SeedBefore qLen p s ∧ p.context.geo.pLen = pLen

theorem refillAttempt_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest)
    (pLen qLen : Nat) (sizes : GenerationSizes pLen qLen) :
    RelCT isa (Two (RefillAttemptBefore pLen qLen))
      (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pLen qLen)
      (fun _ _ => True) := by
  have width : qLen = 20 ∨ qLen = 32 := by
    rcases sizes with h | h | h <;> simp [h.2]
  unfold Impl.Dsa.AArch64.Generation.Refill.refillAttempt
  refine RelCT.seq (two_post
    (two_map (fun p : SeedPublic => p) (fun _ _ h => h.1) (seedSubgroup_ct H T qLen width))
    (fun _ _ h => seedSubgroup_after H T h.1 h.2)) ?_
  apply onSuccess_ct (Φ := SeedSubgroupAfter pLen qLen) SeedPublic.context SeedPublic.subgroupStatus
    (fun _ _ h => h.1) (fun _ _ _ h hm hk => seedSubgroupAfter_congr h hm hk)
  exact two_map SeedPublic.afterSubgroup (fun _ _ h => h.1.2 h.2) (refillPrimeFinish_ct H G T pLen qLen sizes)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of the refillable-tape search's controller on AArch64

The controller's public state between seeds (`LoopPub`): the search's
context, the seeds it may still reject and the seed's start. Whether an
iteration stops, and where the next seed starts, are functions of it
(`ctxContinues`, `ctxNext`), so two runs from the same public state take
the same branches and reach the same public state (`controller_ct`). -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 (upd)
open VG.Proof.Dsa.AArch64.Generation

/-! ## The public state -/

structure LoopPub where
  ctx : GenerationContext
  n : Nat
  c : Nat
  st : BitVec 64
  us : BitVec 64

/-- The pointers to `state` and `used` the search was called with. -/
def PtrsAt (s₀ : State) (P : LoopPub) : Prop := s₀.gpr .x7 = P.st ∧ s₀.gpr .x2 = P.us

/-- Fewer octets than a seed's are left from `c`. -/
def ctxShort (p : GenerationContext) (c : Nat) : Prop := p.rand.bytes.length - c < p.geo.qLen

instance (p : GenerationContext) (c : Nat) : Decidable (ctxShort p c) := by unfold ctxShort; infer_instance

/-- The seed at `c`'s result. -/
def ctxResult (p : GenerationContext) (c : Nat) : Option (Option Spec.Dsa.Params × List Byte) :=
  VG.Proof.Dsa.Generation.refillAttempt p.geo.pLen p.geo.qLen ((p.rand.bytes.drop c).take p.geo.qLen)
    (p.rand.bytes.drop (c + p.geo.qLen))

def ctxContinues (p : GenerationContext) (n c : Nat) : Bool :=
  n != 0 && !decide (ctxShort p c) &&
    match ctxResult p c with
    | some (none, _) => true
    | _ => false

def ctxNext (p : GenerationContext) (c : Nat) : Nat :=
  match ctxResult p c with
  | some (_, rest) => p.rand.bytes.length - rest.length
  | none => c

/-- The status a seed's attempt with result `res` leaves. -/
def resStatus (res : Option (Option Spec.Dsa.Params × List Byte)) : BitVec 64 :=
  match res with
  | none => 0
  | some (none, _) => 3
  | some (some _, _) => 1

def ctxStatus (p : GenerationContext) (c : Nat) : BitVec 64 := resStatus (ctxResult p c)

section
variable {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀)

theorem continues_eq (n c : Nat) : continues h n c = ctxContinues (refillContext h) n c := rfl

theorem nextUsed_eq (c : Nat) : nextUsed h c = ctxNext (refillContext h) c := rfl

end

/-- The controller's state, for some entry of the search. -/
def LoopAt (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧ PtrsAt s₀ P ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t

/-- How the controller ended. -/
def DoneAt (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧ PtrsAt s₀ P ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopDone h v P.n P.c t

/-! ## One iteration -/

theorem two_sp {α : Type} {Φ : α → State → Prop} {c : Prog isa} (hct : RelCT isa (Two Φ) c fun _ _ => True) :
    RelCT isa (Two Φ) c (Two fun (_ : Unit) (_ : State) => True) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, -, -, hsp⟩ := hp
  exact ⟨ht, (), True.intro, True.intro, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

def Started (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧ PtrsAt s₀ P ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t ∧
    ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 P.c ∧ t.gpr .x0 = BitVec.ofNat 64 P.c ∧
    t.gpr .x3 = BitVec.ofNat 64 P.n

theorem started_wp {pBytes : Nat} {P : LoopPub} {t : State} (hl : LoopAt pBytes P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.iterStart) t (Started pBytes P) := by
  obtain ⟨s₀, h, v, hc, hp, hv, hi⟩ := hl
  exact WP.mono (iterStart_ok h (by rw [hv]; exact List.mem_cons_self ..) hi) fun t₁ ⟨a, b, c, d⟩ =>
    ⟨s₀, h, v, hc, hp, hv, a, b, c, d⟩

def Roomed (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State), refillContext h = P.ctx ∧ PtrsAt s₀ P ∧
    v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ LoopState h v P.n P.c t ∧
    ctlWord t.mem (refillBase s₀) 3 = BitVec.ofNat 64 P.c ∧ t.gpr .x0 = BitVec.ofNat 64 P.c ∧
    t.gpr .x3 = BitVec.ofNat 64 (if ctxShort P.ctx P.c then 1 else 0)

theorem roomed_wp {pBytes : Nat} {P : LoopPub} {t : State} (hl : Started pBytes P t) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck (Spec.Dsa.generationQLen pBytes))) t
      (Roomed pBytes P) := by
  obtain ⟨ctx, n, c, st, us⟩ := P
  obtain ⟨s₀, h, v, hc, hp, hv, hi, c3, x0, -⟩ := hl
  subst hc
  exact WP.mono (roomCheck_ok h hi x0) fun t₂ ⟨hi₂, mem₂, x0₂, x3₂⟩ =>
    ⟨s₀, h, v, rfl, hp, hv, hi₂, by rw [ctlWord_eq_of_mem mem₂]; exact c3, x0₂, x3₂⟩

def LoopPub.seedPub (P : LoopPub) (room : P.c + P.ctx.geo.qLen ≤ P.ctx.rand.bytes.length) : SeedPublic where
  context := P.ctx
  seed := P.ctx.rand.slice P.c P.ctx.geo.qLen room
  length := slice_length _ room
  used := P.c + P.ctx.geo.qLen
  seedCursor := 0
  bound := room

/-- Before the seed's attempt. -/
def SeededPub (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  (∃ room, RefillAttemptBefore pBytes (Spec.Dsa.generationQLen pBytes) (P.seedPub room) t) ∧
    Region.Sub ⟨P.ctx.hs.ptr, P.ctx.hs.bytes.length⟩ ⟨P.ctx.rand.ptr, P.ctx.rand.bytes.length⟩

theorem seeded_wp {pBytes : Nat} {P : LoopPub} {t : State}
    (hl : Roomed pBytes P t ∧ isa.eval (.nonzero .x .x3) t = some false) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart (Spec.Dsa.generationQLen pBytes))) t
      (SeededPub pBytes P) := by
  obtain ⟨ctx, n, c, st, us⟩ := P
  obtain ⟨⟨s₀, h, v, hc, -, hv, hi, c3, x0, x3⟩, ev⟩ := hl
  subst hc
  have hq2 : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  have hs : ¬ ctxShort (refillContext h) c := by
    intro hs
    simp only [eval, State.read, x3, BitVec.setWidth_eq, hs, ite_true] at ev
    cases ev
  have room : c + Spec.Dsa.generationQLen pBytes ≤ (randTape h).bytes.length := by
    unfold ctxShort at hs
    change ¬ (randTape h).bytes.length - c < Spec.Dsa.generationQLen pBytes at hs
    omega_using [hq2, hs]
  refine WP.mono (seedStart_ok h hi c3 x0 room) fun t₃ ⟨room', W, hm, w1, w16, w10, seed, _⟩ => ?_
  refine ⟨⟨room', ⟨⟨W, hm, w1, w16, w10⟩, seed, rfl⟩, rfl⟩, ?_⟩
  intro a ha
  simp [Region.Contains, refillContext, GenerationTape.slice] at ha

/-- The status the seed's attempt leaves. -/
theorem outcome_status {p : GenerationContext} {res : Option (Option Spec.Dsa.Params × List Byte)}
    {W : Nat → BitVec 64} {used : Nat} {t : State} (h : SeedOutcome p res W used t) : W 19 = resStatus res := by
  rcases h with ⟨h19, hr⟩ | ⟨h19, hr⟩ | ⟨h19, a, hr, _⟩ <;> subst hr <;> exact h19

def AfterAttempt (P : LoopPub) (t : State) : Prop :=
  ∃ (p : GenerationContext) (W : Nat → BitVec 64), GenerationMemory p W t ∧ W 19 = ctxStatus P.ctx P.c

theorem attempt_wp (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) {pBytes : Nat} {P : LoopPub}
    {t : State} (hl : SeededPub pBytes P t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
      (Spec.Dsa.generationQLen pBytes)) t (AfterAttempt P) := by
  obtain ⟨ctx, n, c, st, us⟩ := P
  obtain ⟨⟨room, ⟨⟨W, hm, h1, h16, _⟩, seed, hq⟩, hp⟩, hsub⟩ := hl
  change ctx.geo.pLen = pBytes at hp
  change ctx.geo.qLen = Spec.Dsa.generationQLen pBytes at hq
  subst hp
  rw [← hq]
  refine WP.mono (refillAttempt_ok H G T hm hsub _ (slice_length _ room) seed h1 h16 room) fun t' hf => ?_
  obtain ⟨hs, W', used, -, hm', -, -, -, outcome, -⟩ := hf
  change SeedOutcome _ (ctxResult ctx c) W' used t' at outcome
  exact ⟨_, W', hm', outcome_status outcome⟩

def StatusTested (P : LoopPub) (t : State) : Prop :=
  isa.eval (.zero .x .x0) t = some (ctxStatus P.ctx P.c == 3)

theorem tested_wp {P : LoopPub} {t : State} (hl : AfterAttempt P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.tapeStatus) t (StatusTested P) := by
  obtain ⟨p, W, hm, h19⟩ := hl
  exact WP.mono (statusTest_ok hm) fun t' ⟨z, _⟩ => by
    show isa.eval _ t' = some (ctxStatus P.ctx P.c == 3)
    rw [← h19]; exact z

theorem nopin {α : Type} (Φ : α → State → Prop) : Pins Φ [] := fun _ _ _ _ _ _ hr => nomatch hr

theorem iteration_ct_of (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes))
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.roomCheck (Spec.Dsa.generationQLen pBytes))) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [])
      (.block (Impl.Dsa.AArch64.Generation.Refill.seedStart (Spec.Dsa.generationQLen pBytes))) hc₂).isSome = true) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) (fun _ _ => True) := by
  simp only [Impl.Dsa.AArch64.Generation.Refill.iteration, VG.Impl.Bignum.AArch64.seqs]
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => started_wp h) ?_
  refine RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True) ?_ (two_taint [] (nopin _) (by taint_decide))
  refine two_ite (fun P s t ⟨_, _, _, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, _, _, ht⟩ => by
    simp only [eval, State.read, hs, ht]) (two_sp (two_taint [] (nopin _) (by taint_decide))) ?_
  refine RelCT.seq (two_piece [] (nopin _) ht₁ fun _ _ h => roomed_wp h.1) ?_
  refine two_ite (fun P s t ⟨_, _, _, _, _, _, _, _, hs⟩ ⟨_, _, _, _, _, _, _, _, ht⟩ => by
    simp only [eval, State.read, hs, ht]) (two_sp (two_taint [] (nopin _) (by taint_decide))) ?_
  refine RelCT.seq (two_piece [] (nopin _) ht₂ fun _ _ h => seeded_wp h) ?_
  refine RelCT.seq (two_post ?_ fun _ _ h => attempt_wp H G T h) ?_
  · refine (refillAttempt_ct H G T pBytes _ sizes).mono ?_ fun _ _ h => h
    rintro s t ⟨P, ⟨⟨room, hs⟩, _⟩, ⟨⟨room', ht⟩, _⟩, hsp⟩
    exact ⟨P.seedPub room, hs, ht, hsp⟩
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => tested_wp h) ?_
  exact two_ite (fun P s t hs ht => hs.trans ht.symm) (two_sp (two_taint [] (nopin _) (by taint_decide)))
    (two_sp (two_taint [] (nopin _) (by taint_decide)))

theorem iteration_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes)) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) (fun _ _ => True) := by
  have hq : Spec.Dsa.generationQLen pBytes = 20 ∨ Spec.Dsa.generationQLen pBytes = 32 := by
    unfold Spec.Dsa.generationQLen; split <;> simp
  rcases hq with hq | hq <;>
    exact iteration_ct_of H G T pBytes sizes (by rw [hq]; taint_decide) (by rw [hq]; taint_decide)

/-! ## The loop -/

/-- After an iteration from `k` seeds left. -/
def StepAt (pBytes k : Nat) (P : LoopPub) (t : State) : Prop :=
  ∃ (s₀ : State) (h : RefillABI pBytes s₀) (v : State),
    refillContext h = P.ctx ∧ PtrsAt s₀ P ∧ v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr ∧ P.n = k ∧ StepPost h v P.n P.c t

/-- The loop's invariant with `k` seeds left. -/
def LoopInv (pBytes k : Nat) : State → State → Prop := Two fun P t => P.n = k ∧ LoopAt pBytes P t

theorem controller_ct (H : GenerationHashes) (G : GeneratorStage) (T : PrimeTest) (pBytes : Nat)
    (sizes : GenerationSizes pBytes (Spec.Dsa.generationQLen pBytes)) :
    RelCT isa (Two (LoopAt pBytes))
      (Impl.Dsa.AArch64.Generation.Refill.controller H.sha1 H.sha256 G.run T.run pBytes
        (Spec.Dsa.generationQLen pBytes)) (Two (DoneAt pBytes)) := by
  have step : ∀ k, RelCT isa (LoopInv pBytes k)
      (Impl.Dsa.AArch64.Generation.Refill.iteration
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes))
      (fun s t => isa.eval (.zero .x .x0) s = isa.eval (.zero .x .x0) t ∧
        (isa.eval (.zero .x .x0) s = some false → Two (DoneAt pBytes) s t) ∧
        (isa.eval (.zero .x .x0) s = some true → ∃ m < k, LoopInv pBytes m s t)) := by
    intro k
    have hA : ∀ {s₀ : State} (h : RefillABI pBytes s₀), AttemptOk h
        (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
          (Spec.Dsa.generationQLen pBytes)) :=
      fun _ hs W t seed hin hm hlen hseed h1 used h16 hu => refillAttempt_ok H G T hm hin seed hlen hseed h1 h16 hu
    have hw : ∀ (P : LoopPub) (t : State), P.n = k ∧ LoopAt pBytes P t →
        WP isa (Impl.Dsa.AArch64.Generation.Refill.iteration
          (Impl.Dsa.AArch64.Generation.Refill.refillAttempt H.sha1 H.sha256 G.run T.run pBytes
            (Spec.Dsa.generationQLen pBytes)) (Spec.Dsa.generationQLen pBytes)) t
          (StepAt pBytes k P) := by
      intro P t ⟨hk, s₀, h, v, hc, hx, hv, hi⟩
      refine WP.mono (step_ok h (hA h) ?_ P.n P.c t hi) fun t' hp => ⟨s₀, h, v, hc, hx, hv, hk, hp⟩
      rw [hv]; exact List.mem_cons_self ..
    have post := two_post (two_map (Φ := fun P t => P.n = k ∧ LoopAt pBytes P t) id (fun _ _ h => h.2)
      (iteration_ct H G T pBytes sizes)) hw
    refine RelCT.mono (P' := LoopInv pBytes k) post (fun _ _ h => h) ?_
    rintro s t ⟨⟨ctx, n, c, sp, us⟩, ⟨s₀, h, v, hc, hx, hv, hk, e, d, k'⟩, ⟨s₀', h', v', hc', hx', hv', -, e', d', k''⟩,
      hsp⟩
    change refillContext h = ctx at hc
    change refillContext h' = ctx at hc'
    have es : isa.eval (.zero .x .x0) s = some (ctxContinues ctx n c) := by
      rw [← hc]; exact e
    have et : isa.eval (.zero .x .x0) t = some (ctxContinues ctx n c) := by
      rw [← hc']; exact e'
    refine ⟨es.trans et.symm, fun ef => ?_, fun et' => ?_⟩
    · have hf : ctxContinues ctx n c = false := Option.some.inj (es.symm.trans ef)
      exact ⟨⟨ctx, n, c, sp, us⟩, ⟨s₀, h, v, hc, hx, hv, d (by rw [continues_eq, hc]; exact hf)⟩,
        ⟨s₀', h', v', hc', hx', hv', d' (by rw [continues_eq, hc']; exact hf)⟩, hsp⟩
    · have ht : ctxContinues ctx n c = true := Option.some.inj (es.symm.trans et')
      obtain ⟨m, hm, st⟩ := k' (by rw [continues_eq, hc]; exact ht)
      obtain ⟨m', hm', st'⟩ := k'' (by rw [continues_eq, hc']; exact ht)
      have e₁ : m' = m := by simp only at hm hm'; omega
      rw [e₁] at st'
      refine ⟨m, by simp only at hk hm; omega, ⟨ctx, m, ctxNext ctx c, sp, us⟩, ⟨rfl, s₀, h, v, hc, hx, hv, ?_⟩,
        ⟨rfl, s₀', h', v', hc', hx', hv', ?_⟩, hsp⟩
      · rw [nextUsed_eq, hc] at st; exact st
      · rw [nextUsed_eq, hc'] at st'; exact st'
  rintro s t a b s' t' ⟨P, hs, ht, hsp⟩ es et
  exact RelCT.loop (LoopInv pBytes) step P.n s t a b s' t' ⟨P, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation.Refill

end

end

/-! ### `Dsa.AArch64.Generation.OutputCT`, which only this module used -/

section

/-! Output copying and failure zeroing use public frame inputs. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Proof.Rsa.AArch64

private theorem ct_assoc_left {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t xs ys u v hp es et
  cases es with
  | seq eab ec =>
    cases eab with
    | seq ea eb =>
      cases et with
      | seq fab fc =>
        cases fab with
        | seq fa fb =>
          obtain ⟨tr, post⟩ := h _ _ _ _ _ _ hp (.seq ea (.seq eb ec)) (.seq fa (.seq fb fc))
          exact ⟨by simpa only [List.append_assoc] using tr, post⟩

structure OutputPublic where
  context : GenerationContext
  accepted : Bool

/-- The frame words the output reads: the arena, `out` and its length, and
the status. -/
def OutputBefore (p : OutputPublic) (s : State) : Prop :=
  ∃ V W, Lay s p.context.geo.F p.context.geo.hash ∧ Rep s.mem p.context.geo.F p.context.geo.hash V W ∧
    W 5 = p.context.saved 5 ∧ W 6 = p.context.saved 6 ∧ W 7 = p.context.saved 7 ∧ (W 19 == (1#64)) = p.accepted

theorem outputBefore_of {p : GenerationContext} {W : Nat → BitVec 64} {s : State} (h : GenerationMemory p W s)
    {a : Bool} (hs : (W 19 == (1#64)) = a) : OutputBefore ⟨p, a⟩ s := by
  obtain ⟨V, R⟩ := h.rep
  exact ⟨V, W, h.layout, R, h.slots 5 (by simp [generationSlots]), h.slots 6 (by simp [generationSlots]),
    h.slots 7 (by simp [generationSlots]), hs⟩

def OutputCopyReady (p : OutputPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off (p.context.saved 5) Impl.Dsa.Generation.Layout.packed ∧
  s.gpr .x2 = p.context.saved 6 ∧ s.gpr .x9 = p.context.saved 7

theorem outputCopy_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.outputCopy
    (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.outputCopy
  refine RelCT.seq (two_post (Ψ := OutputCopyReady) (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
    (two_taint [.x12, .x2, .x9] ?_ (by taint_decide))
  · intro p s ⟨V, W, L, R, h5, h6, h7', _⟩
    have h7 : W 7 = BitVec.ofNat 64 (p.context.saved 7).toNat := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h7'
    exact WP.mono (outputArgs_ok L R h7) fun t ⟨a, b, c, _, _⟩ =>
      show OutputCopyReady p t from ⟨by simpa only [h5] using a,
        b.trans h6, by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c⟩
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.2.2.trans ht.2.2.symm

def OutputZeroReady (p : OutputPublic) (s : State) : Prop :=
  Lay s p.context.geo.F p.context.geo.hash ∧ ∃ V W,
    Rep s.mem p.context.geo.F p.context.geo.hash V W ∧ W 19 = p.context.saved 6 ∧ W 21 = p.context.saved 7

theorem outputZero_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.outputZero
    (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.outputZero zeroOut
  refine RelCT.seq (two_post (Ψ := OutputZeroReady) (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
    (ct_assoc_left (RelCT.seq (two_post (Ψ := fun (p : OutputPublic) s =>
      s.gpr .x11 = p.context.saved 6 ∧ s.gpr .x12 = p.context.saved 7)
      (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_)
      (two_taint [.x11, .x12] ?_ (by taint_decide))))
  · intro p s ⟨V, W, L, R, _, h6, h7, _⟩
    exact WP.mono (zeroArgs_ok L R) fun t ⟨L, R', _, _⟩ =>
      show OutputZeroReady p t from ⟨L, V, _, R', by simpa [upd] using h6, by simpa [upd] using h7⟩
  · intro p s ⟨L, V, W, R, h19, h21⟩
    have ho : s.mem.readW (p.context.geo.F + BitVec.ofNat 64 sOut) 64 = p.context.saved 6 :=
      (R.fr 19 (by decide)).trans h19
    have hk : s.mem.readW (p.context.geo.F + BitVec.ofNat 64 sK) 64 = p.context.saved 7 :=
      (R.fr 21 (by decide)).trans h21
    brun [exec_ldrSp (off := sOut) (by decide), exec_ldrSp (off := sK) (by decide), L.sp,
      L.ld (d := sOut) (n := 8) (by decide), L.ld (d := sK) (n := 8) (by decide), ho, hk]
  · intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

theorem output_check {p : OutputPublic} {s : State} (h : OutputBefore p s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.successStatus) s
      (fun t => OutputBefore p t ∧ isa.eval (.zero .x .x3) t = some p.accepted) := by
  obtain ⟨V, W, L, R, h5, h6, h7, hs⟩ := h
  exact WP.mono (successStatus_ok L R) fun t ⟨hz, he, hk⟩ =>
    ⟨⟨V, W, lay_of_rep L R (he ▸ R) rfl hk.sp hk.wr, he ▸ R, h5, h6, h7, hs⟩, hz.trans (congrArg some hs)⟩

theorem finishOutput_ct : RelCT isa (Two OutputBefore) Impl.Dsa.AArch64.Generation.finishOutput
    (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => output_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) outputCopy_ct
  · exact two_map (fun p : OutputPublic => p) (fun _ _ h => h.1.1) outputZero_ct

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of the refillable-tape search's end on AArch64

`finish`: the words written to `used` and `state`, at the pointers the
controller's words hold, which are public (`PtrsAt`), loaded once into `x14`
and `x15`; the output; the status. Every branch is on the controller's
status and the octets left, functions of its public state. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation.Refill
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Dsa.AArch64.Generation VG.Proof.MlKem.AArch64

/-- The status the controller ends with (`exitStatus`). -/
def ctxExit (p : GenerationContext) (n c : Nat) : Nat :=
  if n = 0 then 2 else if p.rand.bytes.length - c < p.geo.qLen then 0 else
    match ctxResult p c with
    | some (some _, _) => 1
    | _ => 0

theorem exitStatus_eq {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (n c : Nat) :
    exitStatus h n c = ctxExit (refillContext h) n c := rfl

theorem LoopDone.keep {pBytes : Nat} {s₀ : State} {h : RefillABI pBytes s₀} {v : State} {n c : Nat} {t t' : State}
    (hd : LoopDone h v n c t) (hmem : t'.mem = t.mem) {rs : List Reg} (hk : Keep rs t t') : LoopDone h v n c t' := by
  obtain ⟨hs, W, hin, hm, c0, c1, fv, rd, wr, h19, c3, cases⟩ := hd
  refine ⟨hs, W, hin, genMem_keep hm hmem hk, by rw [ctlWord_eq_of_mem hmem]; exact c0,
    by rw [ctlWord_eq_of_mem hmem]; exact c1, by rw [hmem]; exact fv, hk.rd.trans rd, hk.wr.trans wr, h19,
    by rw [ctlWord_eq_of_mem hmem]; exact c3, ?_⟩
  rw [ctlWord_eq_of_mem hmem, hmem]
  exact cases

/-- After the pointers and the status are loaded. -/
def ResStarted (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  DoneAt pBytes P t ∧ t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧ t.gpr .x3 = BitVec.ofNat 64 (ctxExit P.ctx P.n P.c)

theorem resStarted_wp {pBytes : Nat} {P : LoopPub} {t : State} (hd : DoneAt pBytes P t) :
    WP isa (.block Impl.Dsa.AArch64.Generation.Refill.resultsStart) t (ResStarted pBytes P) := by
  obtain ⟨s₀, h, v, hc, ⟨p7, p2⟩, hv, hl⟩ := hd
  have hl' := hl
  obtain ⟨hs, W, _, hm, c0, c1, _, _, wr, h19, _, _⟩ := hl
  obtain ⟨V, R⟩ := hm.rep
  have hv' : (⟨(refillGeometry h).F, 480⟩ : Region) ∈ t.wr := by rw [wr, hv]; exact List.mem_cons_self ..
  refine WP.mono (resultsStart_run hm.layout R hv') fun t₁ ⟨⟨x14, x15, x3, m₁⟩, k₁⟩ =>
    ⟨⟨s₀, h, v, hc, ⟨p7, p2⟩, hv, hl'.keep m₁ k₁⟩, x14.trans (c1.trans p7), x15.trans (c0.trans p2), ?_⟩
  rw [x3, h19, exitStatus_eq, hc]

/-- After a seed that ran out: the octets left reach the budget, or not. -/
def RanOut (pBytes : Nat) (P : LoopPub) (t : State) : Prop :=
  t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧
    t.gpr .x12 = BitVec.ofNat 64 (if 32769 * pBytes ≤ P.ctx.rand.bytes.length - P.c then 1 else 0)

theorem ranOut_wp {pBytes : Nat} {P : LoopPub} {t : State}
    (hr : ResStarted pBytes P t ∧ isa.eval (.zero .x .x3) t = some true) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pBytes)) t (RanOut pBytes P) := by
  obtain ⟨⟨⟨s₀, h, v, hc, -, hv, hl⟩, x14, x15, x3⟩, ev⟩ := hr
  obtain ⟨hs, W, _, hm, _, _, _, _, wr, h19, c3, cases⟩ := hl
  have hp3 : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384 := by
    have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega_using [this]
  have hz : BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) = 0 := by
    simpa [eval, State.read, x3] using ev
  have w0 : W 19 = 0 := by rw [h19, exitStatus_eq, hc]; exact hz
  have hcl : P.c ≤ (randTape h).bytes.length := by
    rcases cases with ⟨e, _⟩ | ⟨_, hc', _⟩ | ⟨e, _⟩
    · rw [w0] at e; cases e
    · exact hc'
    · rw [w0] at e; cases e
  have h15 : W 15 = BitVec.ofNat 64 (randTape h).bytes.length :=
    (hm.slots 15 (by simp [generationSlots])).trans ((refillContext h).withHs hs).randLengthSlot
  obtain ⟨V, R⟩ := hm.rep
  have hv' : (⟨(refillGeometry h).F, 480⟩ : Region) ∈ t.wr := by rw [wr, hv]; exact List.mem_cons_self ..
  refine WP.mono (ranOutCheck_run hm.layout R hv' c3 h15 hcl (randTape h).size hp3)
    fun t₂ ⟨⟨_, _, _, x12, _⟩, k₂⟩ => ⟨(k₂.gpr .x14 (by decide)).trans x14, (k₂.gpr .x15 (by decide)).trans x15, ?_⟩
  rw [x12, ← hc]
  rfl

/-- After the status less one. -/
def Decided (P : LoopPub) (t : State) : Prop :=
  t.gpr .x14 = P.st ∧ t.gpr .x15 = P.us ∧
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) == 1)

theorem decided_wp {pBytes : Nat} {P : LoopPub} {t : State} (hr : ResStarted pBytes P t) :
    WP isa (.block [.subImm .x .x3 .x3 1]) t (Decided P) := by
  obtain ⟨-, x14, x15, x3⟩ := hr
  exact WP.mono minusOne_run fun t₂ ⟨⟨ev, _⟩, k₂⟩ =>
    ⟨(k₂.gpr .x14 (by decide)).trans x14, (k₂.gpr .x15 (by decide)).trans x15, by rw [← x3]; exact ev⟩

theorem pins_ptrs {α : Type} {Φ : α → State → Prop} (st us : α → BitVec 64)
    (h : ∀ a t, Φ a t → t.gpr .x14 = st a ∧ t.gpr .x15 = us a) : Pins Φ [.x14, .x15] := by
  intro a s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h a s hs).1.trans (h a t ht).1.symm
  · exact (h a s hs).2.trans (h a t ht).2.symm

theorem results_ct_of (pBytes : Nat) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (Impl.Dsa.AArch64.Generation.Refill.ranOutCheck pBytes)) hc₁).isSome =
      true) :
    RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.results pBytes) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.Refill.results
  refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => resStarted_wp h) ?_
  refine two_ite (fun P s t ⟨_, _, _, hs⟩ ⟨_, _, _, ht⟩ => by simp only [eval, State.read, hs, ht]) ?_ ?_
  · refine RelCT.seq (two_piece [] (nopin _) ht₁ fun _ _ h => ranOut_wp h) ?_
    refine two_ite (fun P s t ⟨_, _, hs⟩ ⟨_, _, ht⟩ => by simp only [eval, State.read, hs, ht]) ?_ ?_
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
  · refine RelCT.seq (two_piece [] (nopin _) (by taint_decide) fun _ _ h => decided_wp h.1) ?_
    refine two_ite (fun P s t ⟨_, _, hs⟩ ⟨_, _, ht⟩ => hs.trans ht.symm) ?_ ?_
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)
    · exact two_taint _ (pins_ptrs LoopPub.st LoopPub.us fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (by taint_decide)

/-- The output's public state after `results`. -/
def LoopPub.output (P : LoopPub) : OutputPublic := ⟨P.ctx, BitVec.ofNat 64 (ctxExit P.ctx P.n P.c) == (1#64)⟩

theorem results_output {pBytes : Nat} {P : LoopPub} {t : State} (hd : DoneAt pBytes P t) :
    WP isa (Impl.Dsa.AArch64.Generation.Refill.results pBytes) t (OutputBefore P.output) := by
  obtain ⟨ctx, n, c, st, us⟩ := P
  obtain ⟨s₀, h, v, hc, -, hv, hl⟩ := hd
  change refillContext h = ctx at hc
  refine WP.mono (results_ok h hv hl) fun t' D => ?_
  obtain ⟨hs, W, -, -, -, -, -, -, hm, h19, -⟩ := D
  obtain ⟨V, W', L, R, h5, h6, h7, e⟩ := outputBefore_of hm (a := BitVec.ofNat 64 (ctxExit ctx n c) == (1#64))
    (by rw [h19, exitStatus_eq, hc])
  subst hc
  exact ⟨V, W', L, R, h5, h6, h7, e⟩

theorem finish_ct (pBytes : Nat) (hp : pBytes = 128 ∨ pBytes = 256 ∨ pBytes = 384) :
    RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.finish pBytes) (fun _ _ => True) := by
  have results : RelCT isa (Two (DoneAt pBytes)) (Impl.Dsa.AArch64.Generation.Refill.results pBytes)
      (Two OutputBefore) := by
    refine (two_post (Ψ := fun P t => OutputBefore P.output t) ?_ fun _ _ h => results_output h).mono
      (fun _ _ h => h) ?_
    · rcases hp with rfl | rfl | rfl <;> exact results_ct_of _ (by taint_decide)
    · rintro s t ⟨P, hs, ht, hsp⟩
      exact ⟨P.output, hs, ht, hsp⟩
  unfold Impl.Dsa.AArch64.Generation.Refill.finish
  simp only [VG.Impl.Bignum.AArch64.seqs]
  exact RelCT.seq results (RelCT.seq (two_sp finishOutput_ct) (two_taint [] (nopin _) (by taint_decide)))

end VG.Proof.Dsa.AArch64.Generation.Refill
