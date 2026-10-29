module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Impl.Bignum.AArch64.Core

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameStore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameCopy
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameDerived
/-! # ABI arguments and writable regions required to initialize the native search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/FrameStores.lean`, which only this module imported.
section

/-! # Save a list of argument registers into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def registerWords (slots : List (Nat × Reg)) (regs : Reg → BitVec 64) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (regs slot.2)) W

theorem frameStores_ok (slots : List (Nat × Reg)) (bounds : ∀ slot ∈ slots, slot.1 < nW)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) :
    WP isa (.block (slots.map fun slot => .strSp slot.2 (8 * slot.1))) s fun t =>
      Rep t.mem F S V (registerWords slots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block ([_] ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameStore_ok G R hsp hfr (bounds slot (by simp)) slot.2) fun u ⟨Ru, fu, ku⟩ => ?_
    have regs : u.gpr = s.gpr := funext fun r => ku.gpr r (by simp)
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by simp)⟩
    simpa only [registerWords, List.foldl_cons, regs] using Rt

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/FrameCopies.lean`, which only this module imported.
section

/-! # Copy incoming argument words without modifying unread stack arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def copiedWords (slots : List (Nat × Nat)) (values W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.2 (values slot.1)) W

theorem copiedWords_congr (slots : List (Nat × Nat)) (values values' : Nat → BitVec 64)
    (he : ∀ x ∈ slots, values x.1 = values' x.1) (W : Nat → BitVec 64) :
    copiedWords slots values W = copiedWords slots values' W := by
  induction slots generalizing W with
  | nil => rfl
  | cons x xs ih =>
    change copiedWords xs values (upd W x.2 (values x.1)) = copiedWords xs values' (upd W x.2 (values' x.1))
    rw [he x (by simp)]
    exact ih (fun y hy => he y (by simp [hy])) _

theorem frame_input_word {F : Addr} {m m' : Mem} {src : Nat}
    (hf : Frame [⟨F, frameBytes⟩] m m') (hlo : frameBytes ≤ src) (hhi : src + 8 ≤ 2 ^ 64) :
    VG.Proof.Bignum.word m' F src = VG.Proof.Bignum.word m F src := by
  unfold VG.Proof.Bignum.word
  exact hf.readW (r := ⟨VG.Proof.Bignum.off F src, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (Offset.base_disjoint F hlo hhi).symm) (by decide)

theorem frameCopies_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.2 < nW ∧ frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64 ∧ slot.1 % 8 = 0 ∧ slot.1 < 32768)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr)
    (hr : ∀ slot ∈ slots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F slot.1) 8) :
    WP isa (.block (slots.flatMap fun slot => [.ldrSp .x3 slot.1, .strSp .x3 (8 * slot.2)])) s fun t =>
      Rep t.mem F S V (copiedWords slots (VG.Proof.Bignum.word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameCopy_ok G R hsp hfr (bounds slot (by simp)).1 (bounds slot (by simp)).2.2.2 (hr slot (by simp))) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)
      (fun x hx => by rw [ku.rd, ku.wr]; exact hr x (by simp [hx]))) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by decide)⟩
    have same : ∀ x ∈ slots, VG.Proof.Bignum.word u.mem F x.1 = VG.Proof.Bignum.word s.mem F x.1 := by
      intro x hx
      exact frame_input_word fu (bounds x (by simp [hx])).2.1 (bounds x (by simp [hx])).2.2.1
    have eq := copiedWords_congr slots (VG.Proof.Bignum.word u.mem F) (VG.Proof.Bignum.word s.mem F) same (upd W slot.2 (VG.Proof.Bignum.word s.mem F slot.1))
    rw [eq] at Rt
    exact Rt

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/EntryArguments.lean`, which only this module imported.
section

/-! # Save the public ABI arguments before any arithmetic uses their registers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def headerSlots : List (Nat × Reg) :=
  [(6, .x0), (7, .x1), (17, .x2), (18, .x3), (26, .x3), (8, .x4), (9, .x5), (11, .x6), (13, .x7)]

def argumentSlots : List (Nat × Nat) := [(448, 14), (456, 15), (464, 5)]

theorem entryHeader_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryHeader) s fun t =>
      Rep t.mem F S V (registerWords headerSlots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  exact frameStores_ok headerSlots (by
    intro slot hs
    simp only [headerSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) G R hsp hfr

theorem entryIncoming_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F slot.1) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryIncoming) s fun t =>
      Rep t.mem F S V (copiedWords argumentSlots (VG.Proof.Bignum.word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  exact frameCopies_ok argumentSlots (by
    intro slot hs
    simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hr

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/FrameDerivations.lean`, which only this module imported.
section

/-! # Derive several arena pointers from the preserved scratch base -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


def derivedWords (slots : List (Nat × Nat)) (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (VG.Proof.Bignum.off B slot.2)) W

theorem frameDerivations_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.1 < nW ∧ slot.1 ≠ 5 ∧ slot.2 < 65536)
    {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) (hbase : W 5 = B) :
    WP isa (.block (slots.flatMap fun slot => [.ldrSp .x3 40, VG.Impl.Bignum.AArch64.movi .x4 slot.2,
      .add .x .x3 .x3 .x4, .strSp .x3 (8 * slot.1)])) s fun t =>
      Rep t.mem F S V (derivedWords slots B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    have bound := bounds slot (by simp)
    refine WP.mono (frameDerived_ok G R hsp hfr hbase bound.1 bound.2.2) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      (ku.sp.trans hsp) (by rw [ku.wr]; exact hfr)
      (by simpa [upd, Ne.symm bound.2.1] using hbase)) fun t ⟨Rt, ft, kt⟩ => ?_
    exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/EntryDerived.lean`, which only this module imported.
section

/-! # Initialize the three workspace pointers and the witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def workspaceSlots : List (Nat × Nat) := [(3, wrappedSeed), (4, hashes), (12, VG.Impl.Dsa.Generation.Layout.hash)]

def workspaceWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (derivedWords workspaceSlots B W) 16 0

theorem entryDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) (hbase : W 5 = B) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryDerived) s fun t =>
      Rep t.mem F S V (workspaceWords B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  unfold Impl.Dsa.AArch64.Generation.entryDerived
  apply WP.block_append
  refine WP.mono (frameDerivations_ok workspaceSlots (by
    intro slot hs
    simp only [workspaceSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hbase) fun u ⟨Ru, fu, ku⟩ => ?_
  refine WP.mono (frameZero_ok G Ru (ku.sp.trans hsp)
    (by rw [ku.wr]; exact hfr) (by decide : 16 < nW)) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/EntrySetup.lean`, which only this module imported.
section

/-! # Complete ABI argument initialization before size dispatch -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def entryWords (regs : Reg → BitVec 64) (incoming W : Nat → BitVec 64) : Nat → BitVec 64 :=
  workspaceWords (incoming 464) (copiedWords argumentSlots incoming (registerWords headerSlots regs W))

theorem argumentSlots_bounds {slot : Nat × Nat} (hs : slot ∈ argumentSlots) :
    frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64 := by
  simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> decide

theorem entrySetup_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F slot.1) 8) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryIncoming ++
      Impl.Dsa.AArch64.Generation.entryDerived)) s fun t =>
      Rep t.mem F S V (entryWords s.gpr (VG.Proof.Bignum.word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (entryHeader_ok G R hsp hfr) fun u ⟨Ru, fu, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (entryIncoming_ok G Ru (ku.sp.trans hsp)
    (by rw [ku.wr]; exact hfr) (fun slot hs => by rw [ku.rd, ku.wr]; exact hr slot hs))
    fun v ⟨Rv, fv, kv⟩ => ?_
  have words := copiedWords_congr argumentSlots (VG.Proof.Bignum.word u.mem F) (VG.Proof.Bignum.word s.mem F)
    (fun slot hs => frame_input_word fu (argumentSlots_bounds hs).1 (argumentSlots_bounds hs).2)
    (registerWords headerSlots s.gpr W)
  rw [words] at Rv
  have base : copiedWords argumentSlots (VG.Proof.Bignum.word s.mem F) (registerWords headerSlots s.gpr W) 5 = VG.Proof.Bignum.word s.mem F 464 := by
    rfl
  refine WP.mono (entryDerived_ok G Rv ((kv.sp.trans ku.sp).trans hsp)
    (by rw [kv.wr, ku.wr]; exact hfr) base) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, (fu.trans fv).trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

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
  exact ⟨by have := p.geo.stackSize; omega, h.frameTop, p.geo.part_bound hh, p.geo.frame_part hh,
    (p.geo.stack_part hh).sub_left (below_sub (a := 16) (by decide) (by decide)),
    (p.geo.frame_below.sub_right (below_sub (a := 16) (by decide) (by decide))).symm⟩

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
