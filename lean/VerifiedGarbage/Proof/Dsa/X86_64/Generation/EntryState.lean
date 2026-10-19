module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetup
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork

/-! # ABI arguments and writable regions required to initialize the native search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure EntryState (p : GenerationContext) (s : State) : Prop where
  rsp : s.gpr .rsp = p.geo.F
  frame : (⟨p.geo.F, frameBytes⟩ : Region) ∈ s.wr
  frameTop : p.geo.F.toNat + frameBytes + 8 ≤ 2 ^ 64
  scratch : Scr s p.geo.B (usedBytes p.geo.pLen)
  registers : ∀ slot ∈ headerSlots, s.gpr slot.2 = p.saved slot.1
  incoming : ∀ slot ∈ argumentSlots, word s.mem p.geo.F slot.1 = p.saved slot.2
  incomingRead : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (off p.geo.F slot.1) 8
  seeds : GenerationTapeMemory p.seeds s
  hs : GenerationTapeMemory p.hs s
  rand : GenerationTapeMemory p.rand s

theorem EntryState.geometry {p : GenerationContext} {s : State} (h : EntryState p s) : Geo p.geo.F p.geo.hash := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  exact ⟨h.frameTop, p.geo.part_bound hh, p.geo.frame_part hh,
    (p.geo.stack_part hh).sub_left (below_sub (a := 16) (by decide) (by decide))⟩

theorem EntryState.words {p : GenerationContext} {s : State} (h : EntryState p s) (W : Nat → BitVec 64) :
    ∀ k ∈ generationSlots, entryWords s.gpr (word s.mem p.geo.F) W k = p.saved k := by
  have base : word s.mem p.geo.F 384 = p.geo.B :=
    (h.incoming (384, 5) (by simp [argumentSlots])).trans p.baseSlot
  intro k hk
  simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change off (word s.mem p.geo.F 384) wrappedSeed = p.saved 3
    rw [base, p.wrappedSlot]
  · change off (word s.mem p.geo.F 384) hashes = p.saved 4
    rw [base, p.hashesSlot]
  · exact h.incoming (384, 5) (by simp [argumentSlots])
  · exact h.registers (6, .rdi) (by simp [headerSlots])
  · exact h.registers (7, .rsi) (by simp [headerSlots])
  · exact h.registers (8, .r8) (by simp [headerSlots])
  · exact h.registers (9, .r9) (by simp [headerSlots])
  · exact h.incoming (352, 11) (by simp [argumentSlots])
  · exact h.incoming (360, 12) (by simp [argumentSlots])
  · exact h.incoming (368, 13) (by simp [argumentSlots])
  · exact h.incoming (376, 15) (by simp [argumentSlots])
  · exact h.registers (17, .rdx) (by simp [headerSlots])
  · exact h.registers (18, .rcx) (by simp [headerSlots])
  · exact h.registers (28, .rcx) (by simp [headerSlots])

theorem EntryState.hashWord {p : GenerationContext} {s : State} (h : EntryState p s) (W : Nat → BitVec 64) :
    entryWords s.gpr (word s.mem p.geo.F) W 14 = p.geo.hash := by
  change off (word s.mem p.geo.F 384) VG.Impl.Dsa.Generation.Layout.hash = p.geo.hash
  rw [(h.incoming (384, 5) (by simp [argumentSlots])).trans p.baseSlot]
  rfl

end VG.Proof.Dsa.X86_64.Generation
