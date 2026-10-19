module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSearchLoopCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PSearchLoopCT

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
