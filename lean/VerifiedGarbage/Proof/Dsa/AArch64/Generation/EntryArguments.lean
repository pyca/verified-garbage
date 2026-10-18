module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStores
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameCopies

/-! # Save the public ABI arguments before any arithmetic uses their registers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def headerSlots : List (Nat × Reg) :=
  [(6, .x0), (7, .x1), (17, .x2), (18, .x3), (26, .x3), (8, .x4), (9, .x5), (11, .x6), (13, .x7)]

def argumentSlots : List (Nat × Nat) := [(320, 14), (328, 15), (336, 5)]

theorem entryHeader_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryHeader) s fun t =>
      Rep t.mem F S V (registerWords headerSlots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  exact frameStores_ok headerSlots (by
    intro slot hs
    simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) G R hsp hfr

theorem entryIncoming_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F slot.1) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryIncoming) s fun t =>
      Rep t.mem F S V (copiedWords argumentSlots (VG.Proof.Bignum.word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  exact frameCopies_ok argumentSlots (by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hr

end VG.Proof.Dsa.AArch64.Generation
