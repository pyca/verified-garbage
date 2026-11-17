module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Entry
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.AArch64.StackStore
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.Generation.Layout
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! ### `Dsa.AArch64.Generation.RefillABI`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.OutputPlan`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.OutputCopy`, which only this module used -/

section

/-! # Copy accepted packed parameters to the caller and return success -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (VG.Proof.Bignum.off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, VG.Proof.Bignum.off (VG.Proof.Bignum.off (W 5) packed) i ≠ VG.Proof.Bignum.off (W 6) j) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  unfold Impl.Dsa.AArch64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok (by omega_using [hl]) hsi hdi hcx
    (fun i hi => by rw [ku.rd, ku.wr]; exact hrd i hi)
    (fun i hi => by rw [ku.wr]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = v.mem)
    (by brun) rfl rfl rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hl, hi])), hm]

end VG.Proof.Dsa.AArch64.Generation

end

end


/-! # The caller's output is disjoint from every parameter-search workspace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

structure OutputPlan (p : GenerationContext) : Prop where
  lengthSlot : p.saved 7 = BitVec.ofNat 64 (2 * p.geo.pLen + p.geo.qLen)
  bound : (p.saved 6).toNat + (2 * p.geo.pLen + p.geo.qLen) ≤ 2 ^ 64
  separate : ∀ r ∈ p.changed, (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region).Disjoint r

theorem OutputPlan.apart {p : GenerationContext} (o : OutputPlan p) :
    Apart p.geo.F p.geo.hash ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  refine ⟨o.separate ⟨p.geo.F, frameBytes⟩ (by simp [GenerationContext.changed]), ?_, ?_⟩
  · exact (o.separate ⟨p.geo.B, usedBytes p.geo.pLen⟩ (by simp [GenerationContext.changed])).sub_right (p.geo.part_sub hh)
  · exact (o.separate (below p.geo.F 272) (by simp [GenerationContext.changed])).sub_right
      (below_sub (a := 16) (by decide) (by decide))

theorem OutputPlan.packed {p : GenerationContext} (o : OutputPlan p) :
    (p.geo.part packed (2 * p.geo.pLen + p.geo.qLen)).Disjoint ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega_using [h]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with h | h <;> omega_using [h]
  exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right
    (p.geo.part_sub (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])))).symm

theorem output_copy_context {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (bs : List Byte) (hlen : bs.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = bs) :
    WP isa Impl.Dsa.AArch64.Generation.outputCopy s fun t =>
      t.gpr .x0 = 1 ∧ Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) = bs ∧
      Frame [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧ Keep (.x0 :: mmRegs) s t := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have bound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have source : Src s (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) (VG.Proof.Bignum.off p.geo.B packed) bs := by
    apply arena_source h.scratch
    · simpa only [hlen] using bound
    · rw [hlen]; omega_using [pn, qn]
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using o.packed
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h6 := h.slots 6 (by simp [generationSlots])
  have h7 := (h.slots 7 (by simp [generationSlots])).trans o.lengthSlot
  obtain ⟨V, R⟩ := h.rep
  have call := outputCopy_ok h.layout R (by simpa only [hlen] using h7)
    (show 2 ≤ bs.length ∧ bs.length ≤ 1024 by rw [hlen]; omega_using [pn, qn])
  rw [h5, h6, hlen] at call
  apply call
  · intro i hi; exact source.rd i (hlen ▸ hi)
  · intro i hi; exact ⟨_, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi])⟩
  · intro i hi
    simpa only [VG.Proof.Bignum.off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some] using source.val i (hlen ▸ hi)
  · intro i hi j hj he
    apply o.packed (VG.Proof.Bignum.off (VG.Proof.Bignum.off p.geo.B packed) i)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi]))
    rw [he]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [pn, qn, hj])

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The refillable-tape search's precondition on AArch64, as facts about the machine

`vg_dsa_parameter_search(out = x0, out_len = x1, used = x2, rand = x3,
rand_len = x4, scratch = x5, scratch_len = x6, state = x7)`: eight
arguments in registers. Its stack is 768 octets: its frame of 480 and the
288 below it that the attempts' calls use. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 (frameBytes)

/-- The stack the search uses below its stack pointer. -/
abbrev refillStack : Nat := 768

def inOut (s : State) : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .x2, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat * 8⟩
def inState (s : State) : Region := ⟨s.gpr .x7, 32⟩

/-- The modulus's width, `state[1]`. -/
abbrev refillPLen (s : State) : Nat := (s.mem.readW (s.gpr .x7 + 8) 64).toNat

structure RefillABI (pBytes : Nat) (s : State) : Prop where
  width : refillPLen s = pBytes
  stackLower : refillStack ≤ s.sp.toNat
  rd : s.rd = [inRand s]
  wr : s.wr = [inOut s, inUsed s, inScr s, inState s]
  outUsed : (inOut s).Disjoint (inUsed s)
  outScr : (inOut s).Disjoint (inScr s)
  outState : (inOut s).Disjoint (inState s)
  usedScr : (inUsed s).Disjoint (inScr s)
  usedState : (inUsed s).Disjoint (inState s)
  scrState : (inScr s).Disjoint (inState s)
  outRand : (inOut s).Disjoint (inRand s)
  usedRand : (inUsed s).Disjoint (inRand s)
  randScr : (inRand s).Disjoint (inScr s)
  randState : (inRand s).Disjoint (inState s)
  stackOut : (below s.sp refillStack).Disjoint (inOut s)
  stackUsed : (below s.sp refillStack).Disjoint (inUsed s)
  stackRand : (below s.sp refillStack).Disjoint (inRand s)
  stackScr : (below s.sp refillStack).Disjoint (inScr s)
  stackState : (below s.sp refillStack).Disjoint (inState s)
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .x2).toNat + 8 ≤ 2 ^ 64
  randBound : (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64
  scrBound : (s.gpr .x5).toNat + (s.gpr .x6).toNat * 8 ≤ 2 ^ 64
  stateBound : (s.gpr .x7).toNat + 32 ≤ 2 ^ 64
  valid : Spec.Dsa.generationPLenValid (refillPLen s)
  outLength : (s.gpr .x1).toNat = 2 * refillPLen s + Spec.Dsa.generationQLen (refillPLen s)
  scratchLength : Spec.Dsa.generationScratchWords (refillPLen s) ≤ (s.gpr .x6).toNat
  seeds : (s.mem.readW (s.gpr .x7) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (s.gpr .x7 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s))
  randLength : (s.gpr .x4).toNat ≤ Spec.Dsa.parameterEntropy (refillPLen s)

theorem refillABI_of {s : State} (h : (Spec.Dsa.parameterSearchContract abi refillStack).pre s) :
    RefillABI (refillPLen s) s := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs,
    inOut, inUsed, inRand, inScr, inState] at h
  sig_split h
  constructor
  all_goals try simp only [inOut, inUsed, inRand, inScr, inState]
  all_goals first | rfl | with_reducible assumption

/-! ## The frames

The stack below the stack pointer, from `low = sp - 768` up: the 288 octets
the attempts' calls use, then the frame of 480 (`refillBase`): the attempts'
words, the saved registers and the controller's words. -/

def low (s : State) : Addr := s.sp - BitVec.ofNat 64 refillStack

/-- The function's frame. -/
def refillBase (s : State) : Addr := s.sp - BitVec.ofNat 64 480

/-- The controller's words. -/
def ctlRegion (F : Addr) : Region := ⟨off F 448, 32⟩

/-- The controller's `k`-th word. -/
def ctlWord (m : Mem) (F : Addr) (k : Nat) : BitVec 64 := m.readW (off F (448 + 8 * k)) 64

theorem refillBase_low (s : State) : refillBase s = off (low s) 288 := by
  simp only [refillBase, low, off]
  rw [Offset.sub_ofNat_eq s.sp (by decide : 480 ≤ 768)]

theorem refillBase_toNat {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat = s.sp.toNat - 480 := by
  have hl : 768 ≤ s.sp.toNat := h.stackLower
  simp only [refillBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := s.sp.isLt
  omega_using [hl]

theorem low_sub {d n : Nat} (s : State) (h : d + n ≤ refillStack) :
    Region.Sub ⟨off (low s) d, n⟩ (below s.sp refillStack) :=
  Offset.sub_base _ h

theorem refillBase_below (s : State) {n : Nat} (hn : n ≤ 288) :
    below (refillBase s) n = ⟨off (low s) (288 - n), n⟩ := by
  simp only [below, refillBase, low, off]
  congr 1
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, Offset.sub_ofNat_eq s.sp (by omega_using [hn] : 480 + n ≤ 768)]
  congr 2
  omega_using []

theorem ctlRegion_eq (s : State) : ctlRegion (refillBase s) = ⟨off (low s) 736, 32⟩ := by
  simp only [ctlRegion, refillBase_low, off_off]

/-- Regions of the stack below the stack pointer are disjoint from the buffers. -/
theorem RefillABI.stack_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {d n : Nat}
    (hd : d + n ≤ refillStack) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s) :
    (⟨off (low s) d, n⟩ : Region).Disjoint r := by
  have sub := low_sub s hd
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h.stackOut.sub_left sub
  · exact h.stackUsed.sub_left sub
  · exact h.stackRand.sub_left sub
  · exact h.stackScr.sub_left sub
  · exact h.stackState.sub_left sub

/-! ## The search's context -/

theorem RefillABI.lengths {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Spec.Dsa.generationLengthsValid pBytes (Spec.Dsa.generationQLen pBytes) := by
  have hv := h.valid
  rw [h.width] at hv
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
  rcases hv with (rfl | rfl) | rfl <;> decide

theorem RefillABI.scratchSize {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    VG.Impl.Dsa.Generation.Layout.usedBytes pBytes ≤ (s.gpr .x6).toNat * 8 := by
  have hl := VG.Proof.Dsa.Generation.generation_layout_fits h.lengths
  have hs := h.scratchLength
  rw [h.width] at hs
  omega_using [hl, hs]

theorem RefillABI.arena_sub {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Region.Sub ⟨s.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ (inScr s) := by
  simpa [inScr] using (Offset.sub_base (s.gpr .x5) (d := 0) (by simpa using h.scratchSize))

theorem RefillABI.stack_arena {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {d n : Nat}
    (hd : d + n ≤ refillStack) :
    (⟨off (low s) d, n⟩ : Region).Disjoint ⟨s.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ :=
  (h.stack_disjoint hd (r := inScr s) (by simp)).sub_right h.arena_sub

def refillGeometry {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationGeometry where
  B := s.gpr .x5
  F := refillBase s
  pLen := pBytes
  qLen := Spec.Dsa.generationQLen pBytes
  lengths := h.lengths
  arenaBound := by have hb := h.scrBound; have hn := h.scratchSize; omega_using [hb, hn]
  frameBound := by
    rw [refillBase_toNat h]; have hb := s.sp.isLt
    unfold VG.Impl.RsaOaep.AArch64.frameBytes; omega_using []
  stackSize := by rw [refillBase_toNat h]; have hl : 768 ≤ s.sp.toNat := h.stackLower; omega_using [hl]
  frameArena := by rw [refillBase_low]; exact h.stack_arena (by decide)
  stackArena := by rw [refillBase_below s (by decide)]; exact h.stack_arena (by decide)
  callSize := by rw [refillBase_toNat h]; have hl : 768 ≤ s.sp.toNat := h.stackLower; omega_using [hl]
  callArena := by rw [refillBase_below s (by decide)]; exact h.stack_arena (by decide)

/-- The random tape. -/
def randTape {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationTape (refillGeometry h) where
  ptr := s.gpr .x3
  bytes := Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
  bound := by rw [bytesAt_length]; exact h.randBound
  size := by rw [bytesAt_length]; exact (s.gpr .x4).isLt
  arena := by rw [bytesAt_length]; exact h.randScr.sub_right h.arena_sub
  frame := by
    rw [bytesAt_length]
    change (inRand s).Disjoint ⟨refillBase s, frameBytes⟩
    rw [refillBase_low]
    exact (h.stack_disjoint (r := inRand s) (by decide) (by simp)).symm
  stack := by
    rw [bytesAt_length]
    change (inRand s).Disjoint (below (refillBase s) 272)
    rw [refillBase_below s (by decide)]
    exact (h.stack_disjoint (by decide) (by simp)).symm
  callStack := by
    rw [bytesAt_length]
    change (inRand s).Disjoint (below (refillBase s) 288)
    rw [refillBase_below s (by decide)]
    exact (h.stack_disjoint (by decide) (by simp)).symm

/-- The frame words the entry sets. -/
def refillWords (pBytes : Nat) (s : State) : Nat → BitVec 64
  | 3 => off (s.gpr .x5) VG.Impl.Dsa.Generation.Layout.wrappedSeed
  | 4 => off (s.gpr .x5) VG.Impl.Dsa.Generation.Layout.hashes
  | 5 => s.gpr .x5
  | 6 => s.gpr .x0
  | 7 => s.gpr .x1
  | 8 => s.gpr .x3
  | 9 => s.gpr .x4
  | 11 => s.gpr .x3
  | 12 => off (s.gpr .x5) VG.Impl.Dsa.Generation.Layout.hash
  | 13 => 0
  | 14 => s.gpr .x3
  | 15 => s.gpr .x4
  | 17 => BitVec.ofNat 64 pBytes
  | 18 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
  | 26 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
  | _ => 0

def refillContext {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationContext where
  geo := refillGeometry h
  seeds := randTape h
  hs := (randTape h).slice 0 0 (Nat.zero_le _)
  rand := randTape h
  saved := refillWords pBytes s
  wrappedSlot := rfl
  hashesSlot := rfl
  baseSlot := rfl
  seedsSlot := rfl
  seedsLengthSlot := by simp [refillWords, randTape, bytesAt_length]
  hSlot := by simp [refillWords, GenerationTape.slice, randTape, off]
  hLengthSlot := by simp [refillWords, GenerationTape.slice]
  randSlot := rfl
  randLengthSlot := by simp [refillWords, randTape, bytesAt_length]
  pLenSlot := rfl
  qLenSlot := rfl
  hashLenSlot := rfl

theorem refillOutputPlan {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : OutputPlan (refillContext h) where
  lengthSlot := by
    change s.gpr .x1 = BitVec.ofNat 64 (2 * pBytes + Spec.Dsa.generationQLen pBytes)
    rw [← h.width, ← h.outLength]; simp
  bound := by
    change (s.gpr .x0).toNat + (2 * pBytes + Spec.Dsa.generationQLen pBytes) ≤ 2 ^ 64
    rw [← h.width, ← h.outLength]; exact h.outBound
  separate := by
    intro r hr
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (⟨s.gpr .x0, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r
    rw [← h.width, ← h.outLength]
    change (inOut s).Disjoint r
    rcases hr with rfl | rfl | rfl
    · exact h.outScr.sub_right h.arena_sub
    · change (inOut s).Disjoint ⟨refillBase s, frameBytes⟩
      rw [refillBase_low]
      exact (h.stack_disjoint (by decide) (by simp)).symm
    · change (inOut s).Disjoint (below (refillBase s) 272)
      rw [refillBase_below s (by decide)]
      exact (h.stack_disjoint (by decide) (by simp)).symm

end VG.Proof.Dsa.AArch64.Generation.Refill

end

end

/-! ### `Dsa.AArch64.Generation.FrameStore`, which only this module used -/

section

/-! # Initialize frame words before the search scratch pointer has been stored -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

theorem frameWord_write {F : Addr} {k : Nat} (hk : k < nW) (m : Mem) (v : BitVec 64) :
    Frame [⟨F, frameBytes⟩] m (m.writeW (VG.Proof.Bignum.off F (8 * k)) v) :=
  (Frame.refl _ _).writeW (r := ⟨F, frameBytes⟩) (by simp) _
    (Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk]))

theorem initialRep (m : Mem) (F S : Addr) :
    Rep m F S (fun i => m (VG.Proof.Bignum.off S i)) (fun k => VG.Proof.Bignum.word m F (8 * k)) := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.EntryState`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.FrameCopy`, which only this module used -/

section

/-! # Copy incoming stack arguments into the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.FrameDerived`, which only this module used -/

section

/-! # Initialize workspace pointers and cursors in the native generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64


theorem frameDerived_ok {s : State} {F S B : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) (hbase : W 5 = B)
    {k offset : Nat} (hk : k < nW) (hd : offset < 65536) :
    WP isa (.block [.ldrSp .x3 40, VG.Impl.Bignum.AArch64.movi .x4 offset, .add .x .x3 .x3 .x4,
      .strSp .x3 (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k (VG.Proof.Bignum.off B offset)) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  obtain hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk])⟩
  obtain hr : InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off F 40) 8 :=
    Covers.right hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  obtain hread : s.mem.readW (F + BitVec.ofNat 64 40) 64 = B := (R.fr 5 (by decide)).trans hbase
  obtain hv : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using [hd]
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (VG.Proof.Bignum.off B offset))
    (by brun [exec_ldrSp (off := 40) (by decide), exec_storeSp (by unfold nW frameBytes at hk; omega_using [hk] : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hr, hw, VG.Proof.Bignum.off, hread, hv]) rfl rfl rfl)
    fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

theorem frameZero_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (G : Geo F S) (R : Rep s.mem F S V W) (hsp : s.sp = F)
    (hfr : Covers [⟨F, frameBytes⟩] s.wr) {k : Nat} (hk : k < nW) :
    WP isa (.block [VG.Impl.Bignum.AArch64.movi .x3 0, .strSp .x3 (8 * k)]) s fun t =>
      Rep t.mem F S V (upd W k 0) ∧ Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.x3, .x4] s t := by
  obtain hw : InRegions s.wr (VG.Proof.Bignum.off F (8 * k)) 8 :=
    hfr _ _ ⟨⟨F, frameBytes⟩, by simp, Offset.contains_base _ (by unfold nW frameBytes at *; omega_using [hk]) (by unfold nW frameBytes at *; omega_using [hk])⟩
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.mem = s.mem.writeW (VG.Proof.Bignum.off F (8 * k)) (0 : BitVec 64))
    (by brun [exec_storeSp (by unfold nW frameBytes at hk; omega_using [hk] : 8 * k % 8 = 0 ∧ 8 * k < 32768), hsp, hw, VG.Proof.Bignum.off]; rfl) rfl rfl rfl) fun t ⟨hm, kt⟩ => ?_
  exact ⟨hm ▸ R.wf G hk _, hm ▸ frameWord_write hk s.mem _, kt⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # The entry's words derived from the working space's base -/

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
    obtain bound := bounds slot (by simp)
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


end


-- separate module: the entry's symbolic execution, which a change to the loop's proofs does not re-elaborate

/-! # The refillable-tape search's entry on AArch64

The entry stores the arguments in the attempts' frame and the controller's
words (`entry_ok`), and each width's header the subgroup's width
(`widthHeader_ok`). -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation.Refill

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 (Lay Rep Geo upd nW cF)
open VG.Impl.RsaOaep.AArch64 (frameBytes oRsa)
open VG.Proof.Dsa.AArch64.Generation

/-- The memory after the entry's header. -/
def headerMem (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) : Mem :=
  (((((((((((((m.writeW (off F 48) (g .x0)).writeW (off F 56) (g .x1)).writeW (off F 64) (g .x3)).writeW
    (off F 72) (g .x4)).writeW (off F 88) (g .x3)).writeW (off F 112) (g .x3)).writeW (off F 120) (g .x4)).writeW
    (off F 40) (g .x5)).writeW (off F 136) a1).writeW (off F 80) (0 : BitVec 64)).writeW (off F 104) (0 : BitVec 64)).writeW
    (off F 448) (g .x2)).writeW (off F 456) (g .x7)).writeW (off F 464) a0

theorem movz_zero : (BitVec.ofNat 16 0).setWidth 64 = (0 : BitVec 64) := by decide

theorem header_run {s : State} {F : Addr} (hsp : s.sp = F) (hw : (⟨F, 480⟩ : Region) ∈ s.wr)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x7) 8)
    (h8 : InRegions (s.rd ++ s.wr) (s.gpr .x7 + BitVec.ofNat 64 8) 8) :
    WP isa (.block Impl.Dsa.AArch64.Generation.entryHeader) s fun t =>
      t.mem = headerMem s.mem F s.gpr (s.mem.readW (s.gpr .x7) 64)
        (s.mem.readW (s.gpr .x7 + BitVec.ofNat 64 8) 64) ∧ Keep [.x3, .x8, .x9] s t := by
  obtain st : ∀ d, d + 8 ≤ 480 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hw, by rw [hsp]; exact Offset.contains_base F hd (by omega_using [hd])⟩
  refine WP.keep [.x3, .x8, .x9] ?_ (by decide)
  simp only [Impl.Dsa.AArch64.Generation.entryHeader, Impl.Dsa.AArch64.Generation.Refill.ctl, Nat.reduceMul,
    Nat.reduceAdd]
  brun [State.write, exec_ldr_x (off := 0) (by decide), exec_ldr_x (off := 8) (by decide),
    exec_storeSp (off := 48) (by decide), exec_storeSp (off := 56) (by decide),
    exec_storeSp (off := 64) (by decide), exec_storeSp (off := 72) (by decide),
    exec_storeSp (off := 88) (by decide), exec_storeSp (off := 112) (by decide),
    exec_storeSp (off := 120) (by decide), exec_storeSp (off := 40) (by decide),
    exec_storeSp (off := 136) (by decide), exec_storeSp (off := 80) (by decide),
    exec_storeSp (off := 104) (by decide), exec_storeSp (off := 448) (by decide),
    exec_storeSp (off := 456) (by decide), exec_storeSp (off := 464) (by decide), h0, h8,
    st 48 (by decide), st 56 (by decide), st 64 (by decide), st 72 (by decide), st 88 (by decide),
    st 112 (by decide), st 120 (by decide), st 40 (by decide), st 136 (by decide), st 80 (by decide),
    st 104 (by decide), st 448 (by decide), st 456 (by decide), st 464 (by decide), movz_zero]
  rw [hsp]
  rfl

/-! ## The controller's words -/

theorem ctl_contains (F : Addr) {k : Nat} (hk : k < 4) :
    (ctlRegion F).Contains (off F (448 + 8 * k)) 8 :=
  Offset.contains F (e := 448) (by omega_using []) (by omega_using [hk]) (by omega_using [])

theorem ctl_frame (F : Addr) : (ctlRegion F).Disjoint ⟨F, frameBytes⟩ :=
  (Offset.base_disjoint F (e := 448) (n := 32) (k := frameBytes) (by decide) (by omega_using [])).symm

theorem ctl_below (F : Addr) {n : Nat} (hn : n ≤ 288) : (ctlRegion F).Disjoint (below F n) :=
  Offset.disjoint_below F (n := n) (d := 448) (k := 32) (by omega_using [hn])

theorem ctl_write (m : Mem) (F : Addr) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Frame [ctlRegion F] m (m.writeW (off F (448 + 8 * k)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (ctl_contains F hk)

theorem ctlWord_frame {rs : List Region} {m m' : Mem} {F : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (ctlRegion F).Disjoint r) {k : Nat} (hk : k < 4) :
    ctlWord m' F k = ctlWord m F k :=
  hf.readW (ctl_contains F hk) hd (by decide)

theorem ctlWord_write_self (m : Mem) (F : Addr) (k : Nat) (v : BitVec 64) :
    ctlWord (m.writeW (off F (448 + 8 * k)) v) F k = v := Mem.readW_writeW_self64 ..

theorem ctlWord_write_other (m : Mem) (F : Addr) {j k : Nat} (hj : j < 4)
    (hk : k < 4) (hne : j ≠ k) (v : BitVec 64) :
    ctlWord (m.writeW (off F (448 + 8 * k)) v) F j = ctlWord m F j := by
  unfold ctlWord
  rw [Mem.readW_writeW_sep (Offset.sep F (d := 448 + 8 * j) (n := 8) (e := 448 + 8 * k) (k := 8) (by omega_using [hne])
    (by omega_using [hj]) (by omega_using [hk])) (by decide)]

theorem rep_ctl {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Rep (m.writeW (off F (448 + 8 * k)) v) F S V W :=
  rep_of_disjoint_frame R (ctl_write m F hk v)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame F).symm)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact hS.symm)

/-! ## The entry -/

/-- The state the entry starts from: the frame allocated and the
callee-saved registers saved (`linkState`). -/
structure RefillAllocated {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (u : State) : Prop where
  sp : u.sp = refillBase s₀
  wr : u.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr
  rd : u.rd = s₀.rd
  regs : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x7], u.gpr r = s₀.gpr r
  mem : Frame [⟨off (refillBase s₀) 296, 152⟩] s₀.mem u.mem

theorem refillBase_bound {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat + 480 ≤ 2 ^ 64 := by
  rw [refillBase_toNat h]; have := s.sp.isLt; have : 768 ≤ s.sp.toNat := h.stackLower; omega_using []

/-- The regions the entry and the search write in the frame, and the saved
registers', are disjoint from each buffer. -/
theorem RefillABI.frame_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s) {d n : Nat}
    (hd : d + n ≤ 480) : r.Disjoint ⟨off (refillBase s) d, n⟩ := by
  rw [refillBase_low, off_off]
  exact (h.stack_disjoint (by unfold refillStack; omega_using [hd]) hr).symm

theorem RefillABI.geo {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Geo (refillBase s) (refillGeometry h).hash := by
  obtain hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa)
    (by decide) (by decide)
  exact ⟨by
      show 16 ≤ (refillBase s).toNat
      rw [refillBase_toNat h]; have : 768 ≤ s.sp.toNat := h.stackLower; omega_using [this],
    (refillGeometry h).frameBound,
    (refillGeometry h).part_bound hh, (refillGeometry h).frame_part hh,
    ((refillGeometry h).stack_part hh).sub_left (below_sub (a := 16) (by decide) (by decide)),
    ((refillGeometry h).frame_below.sub_right (below_sub (a := 16) (by decide) (by decide))).symm⟩

theorem RefillABI.ctl_arena {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨s.gpr .x5, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  rw [ctlRegion_eq]
  exact h.stack_arena (by decide)

theorem RefillABI.ctl_hash {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  h.ctl_arena.sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

/-- The tape's memory across writes to the frame and the saved registers. -/
theorem RefillAllocated.randMemory {pBytes : Nat} {s₀ u v : State} {h : RefillABI pBytes s₀}
    (a : RefillAllocated h u) (hf : Frame [⟨refillBase s₀, 480⟩] u.mem v.mem)
    (hr : v.rd = u.rd) : GenerationTapeMemory (randTape h) v where
  cover := by
    intro x n hx
    simp only [randTape, bytesAt_length, InRegions, List.mem_singleton] at hx
    obtain ⟨r, rfl, hx⟩ := hx
    refine ⟨_, List.mem_append_left _ ?_, hx⟩
    rw [hr, a.rd, h.rd]; exact List.mem_cons_self ..
  bytes := by
    change Spec.Rsa.bytesAt v.mem (s₀.gpr .x3) (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .x3) (s₀.gpr .x4).toNat).length = _
    rw [bytesAt_length]
    obtain hall : Frame [⟨off (refillBase s₀) 296, 152⟩, ⟨refillBase s₀, 480⟩] s₀.mem v.mem :=
      (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (hf.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; simp)
    refine VG.Proof.Dsa.Generation.frame_bytesAt hall (fun r hr => ?_) (Nat.le_of_lt (s₀.gpr .x4).isLt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.frame_disjoint (r := inRand s₀) (by simp) (by decide)
    · have := h.frame_disjoint (r := inRand s₀) (d := 0) (n := 480) (by simp) (by decide)
      simp only [off, BitVec.add_zero] at this
      exact this

/-- The frame words after the header. -/
def headerWords (W : Nat → BitVec 64) (g : Reg → BitVec 64) (a1 : BitVec 64) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd W 6 (g .x0)) 7 (g .x1)) 8 (g .x3)) 9 (g .x4))
    11 (g .x3)) 14 (g .x3)) 15 (g .x4)) 5 (g .x5)) 17 a1) 10 0) 13 0

theorem headerMem_rep {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    Rep (headerMem m F g a0 a1) F S V (headerWords W g a1) := by
  obtain R1 := ((((((((((R.wf G (k := 6) (by decide) (g .x0)).wf G (k := 7) (by decide) (g .x1)).wf
    G (k := 8) (by decide) (g .x3)).wf G (k := 9) (by decide) (g .x4)).wf G (k := 11) (by decide) (g .x3)).wf
    G (k := 14) (by decide) (g .x3)).wf G (k := 15) (by decide) (g .x4)).wf G (k := 5) (by decide) (g .x5)).wf
    G (k := 17) (by decide) a1).wf G (k := 10) (by decide) 0).wf G (k := 13) (by decide) 0
  exact rep_ctl (rep_ctl (rep_ctl R1 hS (k := 0) (by decide) _) hS (k := 1) (by decide) _) hS (k := 2) (by decide) _

theorem headerMem_frame (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    Frame [⟨F, frameBytes⟩, ctlRegion F] m (headerMem m F g a0 a1) := by
  obtain fc : ∀ d, d + 8 ≤ frameBytes → (⟨F, frameBytes⟩ : Region).Contains (off F d) 8 := fun d hd =>
    Offset.contains_base F hd (by unfold frameBytes at hd; omega_using [hd])
  obtain c : ∀ k < 4, (ctlRegion F).Contains (off F (448 + 8 * k)) 8 := fun _ hk => ctl_contains F hk
  unfold headerMem
  refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW
    (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
    (List.mem_cons_self ..) _ (fc 48 (by decide))) (List.mem_cons_self ..) _ (fc 56 (by decide)))
    (List.mem_cons_self ..) _ (fc 64 (by decide))) (List.mem_cons_self ..) _ (fc 72 (by decide)))
    (List.mem_cons_self ..) _ (fc 88 (by decide))) (List.mem_cons_self ..) _ (fc 112 (by decide)))
    (List.mem_cons_self ..) _ (fc 120 (by decide))) (List.mem_cons_self ..) _ (fc 40 (by decide)))
    (List.mem_cons_self ..) _ (fc 136 (by decide))) (List.mem_cons_self ..) _ (fc 80 (by decide)))
    (List.mem_cons_self ..) _ (fc 104 (by decide))) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 0 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 1 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c 2 (by decide))

theorem headerMem_ctl (m : Mem) (F : Addr) (g : Reg → BitVec 64) (a0 a1 : BitVec 64) :
    ctlWord (headerMem m F g a0 a1) F 0 = g .x2 ∧ ctlWord (headerMem m F g a0 a1) F 1 = g .x7 ∧
      ctlWord (headerMem m F g a0 a1) F 2 = a0 := by
  unfold headerMem
  refine ⟨?_, ?_, ctlWord_write_self _ F 2 _⟩
  · rw [ctlWord_write_other _ F (j := 0) (k := 2) (by decide) (by decide) (by decide),
      ctlWord_write_other _ F (j := 0) (k := 1) (by decide) (by decide) (by decide)]
    exact ctlWord_write_self _ F 0 _
  · rw [ctlWord_write_other _ F (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    exact ctlWord_write_self _ F 1 _

/-- The entry's end: the frame words but the subgroup's width, which each
width's header sets. -/
structure EntryDone {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (W : Nat → BitVec 64) (v : State) :
    Prop where
  layout : Lay v (refillBase s₀) (refillGeometry h).hash
  rep : ∃ V, Rep v.mem (refillBase s₀) (refillGeometry h).hash V W
  slots : ∀ k ∈ generationSlots, k ≠ 18 → k ≠ 26 → W k = refillWords pBytes s₀ k
  w16 : W 16 = 0
  w10 : W 10 = 0
  scratch : Scr v (s₀.gpr .x5) (VG.Impl.Dsa.Generation.Layout.usedBytes pBytes)
  rand : GenerationTapeMemory (randTape h) v
  wr : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr
  rd : v.rd = s₀.rd
  c0 : ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .x2
  c1 : ctlWord v.mem (refillBase s₀) 1 = s₀.gpr .x7
  c2 : ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64

theorem entry_ok {pBytes : Nat} {s₀ u : State} (h : RefillABI pBytes s₀) (a : RefillAllocated h u) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.entryHeader ++ Impl.Dsa.AArch64.Generation.entryDerived)) u
      fun v => ∃ W, EntryDone h W v ∧
        Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem ∧ Keep [.x3, .x4, .x8, .x9] u v := by
  have G := h.geo
  have hS := h.ctl_hash
  obtain hw480 : (⟨refillBase s₀, 480⟩ : Region) ∈ u.wr := by rw [a.wr]; exact List.mem_cons_self ..
  -- `state`'s words, as the entry reads them
  obtain stateSep : (inState s₀).Disjoint ⟨off (refillBase s₀) 296, 152⟩ :=
    h.frame_disjoint (r := inState s₀) (by simp) (by decide)
  obtain c0 : (inState s₀).Contains (s₀.gpr .x7) 8 := by
    have := Offset.contains_base (s₀.gpr .x7) (d := 0) (n := 8) (k := 32) (by decide) (by decide)
    simpa only [inState, BitVec.add_zero] using this
  obtain c8 : (inState s₀).Contains (s₀.gpr .x7 + BitVec.ofNat 64 8) 8 :=
    Offset.contains_base (s₀.gpr .x7) (d := 8) (n := 8) (k := 32) (by decide) (by decide)
  obtain st0 : u.mem.readW (u.gpr .x7) 64 = s₀.mem.readW (s₀.gpr .x7) 64 := by
    rw [a.regs .x7 (by simp)]
    exact a.mem.readW (r := inState s₀) c0
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact stateSep) (by decide)
  obtain st1 : u.mem.readW (u.gpr .x7 + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 pBytes := by
    rw [a.regs .x7 (by simp)]
    rw [a.mem.readW (r := inState s₀) c8
      (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact stateSep) (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← h.width, Nat.mod_eq_of_lt (BitVec.isLt _)]
    rfl
  obtain rd0 : InRegions (u.rd ++ u.wr) (u.gpr .x7) 8 := by
    rw [a.regs .x7 (by simp), a.wr]
    exact ⟨inState s₀, List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr]; simp)), c0⟩
  obtain rd8 : InRegions (u.rd ++ u.wr) (u.gpr .x7 + BitVec.ofNat 64 8) 8 := by
    rw [a.regs .x7 (by simp), a.wr]
    exact ⟨inState s₀, List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [h.wr]; simp)), c8⟩
  apply WP.block_append
  refine WP.mono (header_run a.sp hw480 rd0 rd8) fun t ⟨hm, kt⟩ => ?_
  rw [st0, st1] at hm
  obtain RA := headerMem_rep G (initialRep u.mem (refillBase s₀) (refillGeometry h).hash) hS u.gpr
    (s₀.mem.readW (s₀.gpr .x7) 64) (BitVec.ofNat 64 pBytes)
  rw [← hm] at RA
  obtain fA : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem t.mem := by
    rw [hm]; exact headerMem_frame _ _ _ _ _
  obtain cA := headerMem_ctl u.mem (refillBase s₀) u.gpr (s₀.mem.readW (s₀.gpr .x7) 64) (BitVec.ofNat 64 pBytes)
  rw [← hm] at cA
  obtain spt : t.sp = refillBase s₀ := kt.sp.trans a.sp
  obtain wrt : t.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kt.wr.trans a.wr
  obtain frt : Covers [⟨refillBase s₀, frameBytes⟩] t.wr := by
    rw [wrt]
    have := Offset.contains_base (refillBase s₀) (d := 0) (n := frameBytes) (k := 480) (by decide) (by decide)
    simp only [BitVec.add_zero] at this
    exact Covers.one ⟨_, List.mem_cons_self .., this⟩
  refine WP.mono (entryDerived_ok G RA spt frt (B := u.gpr .x5) rfl) fun v ⟨Rv, fv, kv⟩ => ?_
  obtain fV : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem :=
    fA.trans (fv.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  obtain kV : Keep [.x3, .x4, .x8, .x9] u v := (kt.trans kv).mono (by decide)
  obtain r5 : u.gpr .x5 = s₀.gpr .x5 := a.regs _ (by simp)
  obtain spv : v.sp = refillBase s₀ := kV.sp.trans a.sp
  obtain wrv : v.wr = ⟨refillBase s₀, 480⟩ :: s₀.wr := kV.wr.trans a.wr
  obtain scr : Scr v (s₀.gpr .x5) (VG.Impl.Dsa.Generation.Layout.usedBytes pBytes) :=
    ⟨⟨s₀.gpr .x5, 0, (s₀.gpr .x6).toNat * 8, by rw [wrv]; exact List.mem_cons_of_mem _ (by rw [h.wr]; simp [inScr]),
      by simp [off], by have := h.scratchSize; omega_using [this], by have := h.scrBound; omega_using [this]⟩,
      by have := h.scrBound; have := h.scratchSize; omega_arith⟩
  obtain hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  obtain ctlV : ∀ k < 4, ctlWord v.mem (refillBase s₀) k = ctlWord t.mem (refillBase s₀) k := fun k hk =>
    ctlWord_frame fv (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame _) hk
  obtain fV480 : Frame [⟨refillBase s₀, 480⟩] u.mem v.mem := fV.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · have := Offset.sub_base (refillBase s₀) (d := 0) (n := frameBytes) (k := 480) (by decide)
      simpa only [BitVec.add_zero] using this
    · exact Offset.sub_base (refillBase s₀) (d := 448) (n := 32) (k := 480) (by decide)
  refine ⟨_, ⟨?_, ⟨_, Rv⟩, ?_, ?_, by simp [workspaceWords, derivedWords, workspaceSlots, headerWords, upd], scr, a.randMemory fV480 kV.rd, wrv, kV.rd.trans a.rd, ?_, ?_, ?_⟩, fV, kV⟩
  · exact { sp := spv
            fr := by rw [kv.wr]; exact frt
            sc := Covers.one (scr.region hh (by decide))
            slot := by
              show VG.Proof.RsaOaep.AArch64.word v.mem (refillBase s₀) (8 * 12) = (refillGeometry h).hash
              rw [Rv.fr 12 (by decide)]
              simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, upd, r5]
              rfl
            geo := G }
  · intro k hk h18 h26
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl h18 | exact absurd rfl h26 | skip
    all_goals simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, headerWords, upd, refillWords,
      r5, a.regs .x0 (by simp), a.regs .x1 (by simp), a.regs .x3 (by simp), a.regs .x4 (by simp)]
    all_goals first | rfl | simp [off]
  · simp [workspaceWords, upd]
  · rw [ctlV 0 (by decide), cA.1, a.regs .x2 (by simp)]
  · rw [ctlV 1 (by decide), cA.2.1, a.regs .x7 (by simp)]
  · rw [ctlV 2 (by decide), cA.2.2]

/-- The subgroup's width in `W 18` and `W 26`: the search's memory. -/
theorem widthHeader_ok {pBytes qBytes : Nat} {s₀ v : State} {h : RefillABI pBytes s₀} {W : Nat → BitVec 64}
    (E : EntryDone h W v) (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.Refill.widthHeader qBytes)) v fun w =>
      GenerationMemory (refillContext h) (upd (upd W 18 (BitVec.ofNat 64 qBytes)) 26 (BitVec.ofNat 64 qBytes)) w ∧
      W 16 = 0 ∧ W 10 = 0 ∧ ctlWord w.mem (refillBase s₀) 0 = s₀.gpr .x2 ∧ ctlWord w.mem (refillBase s₀) 1 = s₀.gpr .x7 ∧
      ctlWord w.mem (refillBase s₀) 2 = s₀.mem.readW (s₀.gpr .x7) 64 ∧
      Frame [⟨refillBase s₀, frameBytes⟩] v.mem w.mem ∧ Keep [.x3] v w := by
  have L := E.layout
  obtain ⟨V, R⟩ := E.rep
  obtain hq32 : qBytes < 2 ^ 16 := by subst hq; unfold Spec.Dsa.generationQLen; split <;> decide
  obtain hmv : (BitVec.ofNat 16 qBytes).setWidth 64 = BitVec.ofNat 64 qBytes := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hq32]
  obtain hq2 : qBytes = 20 ∨ qBytes = 32 := by subst hq; unfold Spec.Dsa.generationQLen; split <;> simp
  obtain s144 : InRegions v.wr (v.sp + BitVec.ofNat 64 144) 8 := by rw [L.sp]; exact L.st (d := 144) (by decide)
  obtain s208 : InRegions v.wr (v.sp + BitVec.ofNat 64 208) 8 := by rw [L.sp]; exact L.st (d := 208) (by decide)
  refine WP.mono (WP.keep [.x3] (Q := fun w => w.mem = (v.mem.writeW (off (refillBase s₀) 144) (BitVec.ofNat 64 qBytes)).writeW
      (off (refillBase s₀) 208) (BitVec.ofNat 64 qBytes)) (by
    unfold Impl.Dsa.AArch64.Generation.Refill.widthHeader
    brun [State.write, exec_storeSp (off := 144) (by decide), exec_storeSp (off := 208) (by decide), s144, s208, hmv]
    rw [L.sp]) (by rcases hq2 with rfl | rfl <;> decide) rfl
    (by rcases hq2 with rfl | rfl <;> decide +kernel)) fun w ⟨hm, kw⟩ => ?_
  obtain Rw : Rep w.mem (refillBase s₀) (refillGeometry h).hash V
      (upd (upd W 18 (BitVec.ofNat 64 qBytes)) 26 (BitVec.ofNat 64 qBytes)) := by
    rw [hm]; exact (R.wf L.geo (k := 18) (by decide) _).wf L.geo (k := 26) (by decide) _
  obtain fw : Frame [⟨refillBase s₀, frameBytes⟩] v.mem w.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (cF _ (d := 144) (by decide))).writeW
      List.mem_cons_self _ (cF _ (d := 208) (by decide))
  obtain cw : ∀ k < 4, ctlWord w.mem (refillBase s₀) k = ctlWord v.mem (refillBase s₀) k := fun k hk =>
    ctlWord_frame fw (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame _) hk
  obtain fc : Frame (refillContext h).changed v.mem w.mem := GenerationContext.frame_single fw
  obtain randW : GenerationTapeMemory (randTape h) w :=
    E.rand.frame (p := refillContext h) fc kw.rd kw.wr
  refine ⟨⟨lay_of_rep L R Rw (by simp [upd]) kw.sp kw.wr, ⟨V, Rw⟩, ?_, E.scratch.congr kw.wr, randW,
    randW.slice (Nat.zero_le _), randW⟩, E.w16, E.w10, by rw [cw 0 (by decide)]; exact E.c0,
    by rw [cw 1 (by decide)]; exact E.c1, by rw [cw 2 (by decide)]; exact E.c2, fw, kw⟩
  intro k hk
  by_cases h18 : k = 18
  · subst h18; simp [upd, refillContext, refillWords, hq]
  by_cases h26 : k = 26
  · subst h26; simp [upd, refillContext, refillWords, hq]
  simp only [upd, h18, h26, ite_false]
  exact E.slots k hk h18 h26

end VG.Proof.Dsa.AArch64.Generation.Refill
