module

public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeometryWork
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Context
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecOut
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Output
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CopyBytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ArenaSource
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

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
