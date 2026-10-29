module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameDerived
/-! # ABI arguments and writable regions required to initialize the native search -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FrameStores.lean`, which only this module imported.
section

/-! # Save a list of argument registers into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def registerWords (slots : List (Nat × Reg)) (regs : Reg → BitVec 64) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (regs slot.2)) W

theorem frameStores_ok (slots : List (Nat × Reg)) (bounds : ∀ slot ∈ slots, slot.1 < nW)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) :
    WP isa (.block (slots.map fun slot => .store (sp (8 * slot.1)) slot.2)) s fun t =>
      Rep t.mem F S V (registerWords slots s.gpr W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block ([_] ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameStore_ok G R hsp hfr (bounds slot (by simp)) slot.2) fun u ⟨Ru, fu, ku⟩ => ?_
    have regs : u.gpr = s.gpr := funext fun r => ku.gpr (by simp)
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by simp)).trans hsp) (by rw [ku.2.2]; exact hfr)) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by simp)⟩
    simpa only [registerWords, List.foldl_cons, regs] using Rt

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FrameCopy.lean`, which only this module imported.
section

/-! # Copy incoming stack arguments into the persistent frame -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

theorem frameCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) {k src : Nat} (hk : k < nW)
    (hr : InRegions (s.rd ++ s.wr) (off F src) 8) :
    WP isa (.block [.mov .rax (.mem (sp src)), .store (sp (8 * k)) .rax]) s fun t =>
      Rep t.mem F S V (upd W k (word s.mem F src)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have hw : InRegions s.wr (off F (8 * k)) 8 :=
    ⟨_, hfr, Offset.contains_base _ (by unfold nW frameBytes at *; omega) (by unfold nW frameBytes at *; omega)⟩
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off F (8 * k)) (word s.mem F src))
    (by xrun [ea_sp, hsp, hr, hw, VG.Proof.Bignum.word]) rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FrameCopies.lean`, which only this module imported.
section

/-! # Copy incoming argument words without modifying unread stack arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

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
    word m' F src = word m F src := by
  unfold VG.Proof.Bignum.word
  exact hf.readW (r := ⟨off F src, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact (Offset.base_disjoint F hlo hhi).symm) (by decide)

theorem frameCopies_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.2 < nW ∧ frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64)
    {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr)
    (hr : ∀ slot ∈ slots, InRegions (s.rd ++ s.wr) (off F slot.1) 8) :
    WP isa (.block (slots.flatMap fun slot => [.mov .rax (.mem (sp slot.1)), .store (sp (8 * slot.2)) .rax])) s fun t =>
      Rep t.mem F S V (copiedWords slots (word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    refine WP.mono (frameCopy_ok G R hsp hfr (bounds slot (by simp)).1 (hr slot (by simp))) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by decide)).trans hsp) (by rw [ku.2.2]; exact hfr)
      (fun x hx => by rw [ku.2.1, ku.2.2]; exact hr x (by simp [hx]))) fun t ⟨Rt, ft, kt⟩ => ?_
    refine ⟨?_, fu.trans ft, (ku.trans kt).mono (by decide)⟩
    have same : ∀ x ∈ slots, word u.mem F x.1 = word s.mem F x.1 := by
      intro x hx
      exact frame_input_word fu (bounds x (by simp [hx])).2.1 (bounds x (by simp [hx])).2.2
    have eq := copiedWords_congr slots (word u.mem F) (word s.mem F) same (upd W slot.2 (word s.mem F slot.1))
    rw [eq] at Rt
    exact Rt

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryArguments.lean`, which only this module imported.
section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/FrameDerivations.lean`, which only this module imported.
section

/-! # Derive several arena pointers from the preserved scratch base -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

def derivedWords (slots : List (Nat × Nat)) (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  slots.foldl (fun words slot => upd words slot.1 (off B slot.2)) W

theorem frameDerivations_ok (slots : List (Nat × Nat))
    (bounds : ∀ slot ∈ slots, slot.1 < nW ∧ slot.1 ≠ 5 ∧ slot.2 < 2 ^ 31)
    {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block (slots.flatMap fun slot => [.mov .rax (.mem (sp 40)),
      .alu .add .rax (.imm (BitVec.ofNat 32 slot.2)), .store (sp (8 * slot.1)) .rax])) s fun t =>
      Rep t.mem F S V (derivedWords slots B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  induction slots generalizing s W with
  | nil => exact WP.block_nil ⟨R, Frame.refl _ _, Keep.refl _ _⟩
  | cons slot slots ih =>
    change WP isa (.block (_ ++ _)) s _
    apply WP.block_append
    have bound := bounds slot (by simp)
    refine WP.mono (frameDerived_ok G R hsp hfr hbase bound.1 bound.2.2) fun u ⟨Ru, fu, ku⟩ => ?_
    refine WP.mono (ih (fun x hx => bounds x (by simp [hx])) Ru
      ((ku.gpr (by decide)).trans hsp) (by rw [ku.2.2]; exact hfr)
      (by simpa [upd, Ne.symm bound.2.1] using hbase)) fun t ⟨Rt, ft, kt⟩ => ?_
    exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryDerived.lean`, which only this module imported.
section

/-! # Initialize the three workspace pointers and the witness cursor -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

def workspaceSlots : List (Nat × Nat) := [(3, wrappedSeed), (4, hashes), (14, VG.Impl.Dsa.Generation.Layout.hash)]

def workspaceWords (B : Addr) (W : Nat → BitVec 64) : Nat → BitVec 64 :=
  upd (derivedWords workspaceSlots B W) 16 0

theorem entryDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hbase : W 5 = B) :
    WP isa (.block Impl.Dsa.X86_64.Generation.entryDerived) s fun t =>
      Rep t.mem F S V (workspaceWords B W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  unfold Impl.Dsa.X86_64.Generation.entryDerived
  apply WP.block_append
  refine WP.mono (frameDerivations_ok workspaceSlots (by
    intro slot hs
    simp only [workspaceSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide) G R hsp hfr hbase) fun u ⟨Ru, fu, ku⟩ => ?_
  refine WP.mono (frameZero_ok G Ru ((ku.gpr (by decide)).trans hsp)
    (by rw [ku.2.2]; exact hfr) (by decide : 16 < nW)) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, fu.trans ft, (ku.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntrySetup.lean`, which only this module imported.
section

/-! # Complete ABI argument initialization before size dispatch -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def entryWords (regs : Reg → BitVec 64) (incoming W : Nat → BitVec 64) : Nat → BitVec 64 :=
  workspaceWords (incoming 384) (copiedWords argumentSlots incoming (registerWords headerSlots regs W))

theorem argumentSlots_bounds {slot : Nat × Nat} (hs : slot ∈ argumentSlots) :
    frameBytes ≤ slot.1 ∧ slot.1 + 8 ≤ 2 ^ 64 := by
  simp only [argumentSlots, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem entrySetup_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr)
    (hr : ∀ slot ∈ argumentSlots, InRegions (s.rd ++ s.wr) (off F slot.1) 8) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.entryHeader ++ Impl.Dsa.X86_64.Generation.entryIncoming ++
      Impl.Dsa.X86_64.Generation.entryDerived)) s fun t =>
      Rep t.mem F S V (entryWords s.gpr (word s.mem F) W) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (entryHeader_ok G R hsp hfr) fun u ⟨Ru, fu, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (entryIncoming_ok G Ru ((ku.gpr (by simp)).trans hsp)
    (by rw [ku.2.2]; exact hfr) (fun slot hs => by rw [ku.2.1, ku.2.2]; exact hr slot hs))
    fun v ⟨Rv, fv, kv⟩ => ?_
  have words := copiedWords_congr argumentSlots (word u.mem F) (word s.mem F)
    (fun slot hs => frame_input_word fu (argumentSlots_bounds hs).1 (argumentSlots_bounds hs).2)
    (registerWords headerSlots s.gpr W)
  rw [words] at Rv
  have base : copiedWords argumentSlots (word s.mem F) (registerWords headerSlots s.gpr W) 5 = word s.mem F 384 := by
    rfl
  refine WP.mono (entryDerived_ok G Rv ((kv.gpr (by decide)).trans ((ku.gpr (by simp)).trans hsp))
    (by rw [kv.2.2, ku.2.2]; exact hfr) base) fun t ⟨Rt, ft, kt⟩ => ?_
  exact ⟨Rt, (fu.trans fv).trans ft, ((ku.trans kv).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

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
