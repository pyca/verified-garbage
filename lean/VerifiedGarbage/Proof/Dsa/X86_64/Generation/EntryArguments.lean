module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStores
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameCopies
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Save the public ABI arguments before any arithmetic uses their registers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def headerSlots : List (Nat × Reg) := [(6, .rdi), (7, .rsi), (17, .rdx), (18, .rcx), (28, .rcx), (8, .r8), (9, .r9)]

def argumentSlots : List (Nat × Nat) := [(352, 11), (360, 12), (368, 13), (376, 15), (384, 5)]

theorem entryHeader_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.Dsa.X86_64.Generation.entryHeader) s fun t =>
      Rep t.mem F S V (registerWords headerSlots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  exact frameStores_ok headerSlots (by
    intro slot hs
    simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) G R hsp hfr

theorem entryIncoming_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (off F slot.1) 8) :
    WP isa (.block Impl.Dsa.X86_64.Generation.entryIncoming) s fun t =>
      Rep t.mem F S V (copiedWords argumentSlots (word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  exact frameCopies_ok argumentSlots (by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide) G R hsp hfr hr

end VG.Proof.Dsa.X86_64.Generation
