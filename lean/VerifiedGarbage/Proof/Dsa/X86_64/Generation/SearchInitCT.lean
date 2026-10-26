module
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptBlocksCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptBlocksCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStable
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration
import Mathlib.Data.Int.ModEq

/-! # Initialize the bounded p search without assumptions about old controller words -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.X86_64.Generation

def SearchStart (n pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  (∃ W, SearchMemory p.plan W s ∧ W 16 = BitVec.ofNat 64 p.used) ∧
    Scr s p.plan.C 24 ∧ FrV n p.plan.attempt.construct.hash.F p.ws s ∧ s.wr = p.wr ∧
    p.used ≤ p.plan.attempt.rand.length ∧ p.plan.attempt.construct.len = pLen ∧
    p.plan.attempt.construct.hash.len = qLen ∧ p.counter = 0

def SearchInitBefore (n pLen qLen : Nat) (p : SearchPublic) (s : State) : Prop :=
  SearchStart n pLen qLen p s ∧ s.gpr .rdi = p.plan.C

def SearchPublic.returnFrame (p : SearchPublic) : AttemptReturnPublic :=
  ⟨p.plan.attempt.construct.hash.F, p.plan.attempt.construct.hash.S, p.plan.attempt.construct.hash.W 5⟩

theorem searchStart_frame {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchStart n pLen qLen p s) : AttemptReturnBefore p.returnFrame s := by
  obtain ⟨W, memory, _⟩ := h.1
  obtain ⟨V, R⟩ := memory.rep
  exact ⟨memory.layout, V, W, R, memory.slots 5 (by simp [searchSlots])⟩

theorem searchBase_ready {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchStart n pLen qLen p s) :
    WP isa (.block controlBase) s (SearchInitBefore n pLen qLen p) := by
  obtain ⟨⟨W, memory, used⟩, scr, frame, wr, bound, hp, hq, counter⟩ := h
  obtain ⟨V, R⟩ := memory.rep
  have base : W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.control = p.plan.C := by
    rw [memory.slots 5 (by simp [searchSlots])]; exact p.plan.controlBase
  refine WP.mono (controlBase_ok memory.layout R base) fun t ⟨hdi, hm, hk⟩ => ?_
  have L := memory.layout.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have mt := memory.frame L ⟨V, hm ▸ R⟩ (fun _ _ => rfl)
    (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2
  exact ⟨⟨⟨W, mt, used⟩, scr.congr hk.2.2, frame.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans wr, bound, hp, hq, counter⟩, hdi⟩

theorem searchInit_ready {n pLen qLen : Nat} {p : SearchPublic} {s : State}
    (h : SearchInitBefore n pLen qLen p s) :
    WP isa (.block pSearchInit) s (SearchBefore n pLen qLen p) := by
  obtain ⟨⟨⟨W, memory, used⟩, scr, frame, wr, bound, hp, hq, counter⟩, hdi⟩ := h
  refine WP.mono (searchInit_ok scr hdi (p.plan.attempt.construct.hash.count + 1))
    fun t ⟨ctrl, ff, hk⟩ => ?_
  have mt := SearchMemory.stable memory (ff.mono (by decide) (by decide)) (hk.mono (by decide))
  exact ⟨⟨W, mt, used⟩, (by rw [counter]; exact ctrl), frame.congr (hk.gpr (by decide)) hk.2.2,
    hk.2.2.trans wr, bound, hp, hq⟩

theorem searchInit_ct (n pLen qLen : Nat) :
    RelCT isa (Two (SearchInitBefore n pLen qLen)) (.block pSearchInit) (Two (SearchBefore n pLen qLen)) := by
  refine two_post (two_taint [.rdi] ?_ (by taint_decide)) (fun _ _ h => searchInit_ready h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr; subst r
  exact hs.2.trans ht.2.symm

end VG.Proof.Dsa.X86_64.Generation
