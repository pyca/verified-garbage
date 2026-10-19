module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySetup
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Framework.Omega

/-! # ABI arguments and writable regions required to initialize the native search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure EntryState (p : GenerationContext) (s : State) : Prop where
  sp : s.sp = p.geo.F
  frame : Covers [⟨p.geo.F, frameBytes⟩] s.wr
  frameTop : p.geo.F.toNat + frameBytes ≤ 2 ^ 64
  scratch : Scr s p.geo.B (usedBytes p.geo.pLen)
  registers : ∀ slot ∈ headerSlots, s.gpr slot.2 = p.saved slot.1
  incoming : ∀ slot ∈ argumentSlots, VG.Proof.Bignum.word s.mem p.geo.F slot.1 = p.saved slot.2
  incomingRead : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off p.geo.F slot.1) 8
  hashScratch : p.saved 12 = p.geo.hash
  seeds : GenerationTapeMemory p.seeds s
  hs : GenerationTapeMemory p.hs s
  rand : GenerationTapeMemory p.rand s

theorem EntryState.geometry {p : GenerationContext} {s : State} (h : EntryState p s) : Geo p.geo.F p.geo.hash := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  exact ⟨p.geo.stackSize, h.frameTop, p.geo.part_bound hh, p.geo.frame_part hh,
    p.geo.stack_part hh, p.geo.frame_below.symm⟩

theorem EntryState.words {p : GenerationContext} {s : State} (h : EntryState p s) (W : Nat → BitVec 64) :
    ∀ k ∈ generationSlots, entryWords s.gpr (VG.Proof.Bignum.word s.mem p.geo.F) W k = p.saved k := by
  have base : VG.Proof.Bignum.word s.mem p.geo.F 464 = p.geo.B :=
    (h.incoming (464, 5) (by simp [argumentSlots])).trans p.baseSlot
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change VG.Proof.Bignum.off (VG.Proof.Bignum.word s.mem p.geo.F 464) wrappedSeed = p.saved 3
    rw [base, p.wrappedSlot]
  · change VG.Proof.Bignum.off (VG.Proof.Bignum.word s.mem p.geo.F 464) hashes = p.saved 4
    rw [base, p.hashesSlot]
  · exact h.incoming (464, 5) (by simp [argumentSlots])
  · exact h.registers (6, .x0) (by simp [headerSlots])
  · exact h.registers (7, .x1) (by simp [headerSlots])
  · exact h.registers (8, .x4) (by simp [headerSlots])
  · exact h.registers (9, .x5) (by simp [headerSlots])
  · exact h.registers (11, .x6) (by simp [headerSlots])
  · change VG.Proof.Bignum.off (VG.Proof.Bignum.word s.mem p.geo.F 464) VG.Impl.Dsa.Generation.Layout.hash = p.saved 12
    rw [base, h.hashScratch]
    rfl
  · exact h.registers (13, .x7) (by simp [headerSlots])
  · exact h.incoming (448, 14) (by simp [argumentSlots])
  · exact h.incoming (456, 15) (by simp [argumentSlots])
  · exact h.registers (17, .x2) (by simp [headerSlots])
  · exact h.registers (18, .x3) (by simp [headerSlots])
  · exact h.registers (26, .x3) (by simp [headerSlots])

theorem EntryState.hashWord {p : GenerationContext} {s : State} (h : EntryState p s) (W : Nat → BitVec 64) :
    entryWords s.gpr (VG.Proof.Bignum.word s.mem p.geo.F) W 12 = p.geo.hash :=
  (h.words W 12 (by simp [generationSlots])).trans h.hashScratch

end VG.Proof.Dsa.AArch64.Generation
