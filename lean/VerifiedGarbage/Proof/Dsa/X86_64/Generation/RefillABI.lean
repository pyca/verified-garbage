module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The refillable-tape search's precondition, as facts about the machine

`vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` for one width: six arguments in registers and two on
the stack. Its stack is 568 octets: the saved registers' 48, the
controller's 32, the attempts' 296 and the 192 below them that the attempts'
calls use. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack the search uses below its return address. -/
abbrev stackUse : Nat := 568

def inOut (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 1, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The modulus's width, `state[1]`. -/
abbrev refillPLen (s : State) : Nat := (s.mem.readW (stackArg s 1 + 8) 64).toNat

structure RefillABI (pBytes : Nat) (s : State) : Prop where
  stackLower : stackUse ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [inRand s, inArgs s]
  wr : s.wr = [inOut s, inUsed s, inScr s, inState s]
  outUsed : (inOut s).Disjoint (inUsed s)
  outRand : (inOut s).Disjoint (inRand s)
  outScr : (inOut s).Disjoint (inScr s)
  outState : (inOut s).Disjoint (inState s)
  outArgs : (inOut s).Disjoint (inArgs s)
  usedRand : (inUsed s).Disjoint (inRand s)
  usedScr : (inUsed s).Disjoint (inScr s)
  usedState : (inUsed s).Disjoint (inState s)
  usedArgs : (inUsed s).Disjoint (inArgs s)
  randScr : (inRand s).Disjoint (inScr s)
  randState : (inRand s).Disjoint (inState s)
  scrState : (inScr s).Disjoint (inState s)
  scrArgs : (inScr s).Disjoint (inArgs s)
  stateArgs : (inState s).Disjoint (inArgs s)
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inOut s)
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inUsed s)
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inRand s)
  retScr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inScr s)
  retState : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inState s)
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inArgs s)
  stackOut : (below (s.gpr .rsp) stackUse).Disjoint (inOut s)
  stackUsed : (below (s.gpr .rsp) stackUse).Disjoint (inUsed s)
  stackRand : (below (s.gpr .rsp) stackUse).Disjoint (inRand s)
  stackScr : (below (s.gpr .rsp) stackUse).Disjoint (inScr s)
  stackState : (below (s.gpr .rsp) stackUse).Disjoint (inState s)
  stackArgs : (below (s.gpr .rsp) stackUse).Disjoint (inArgs s)
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  randBound : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  scrBound : (s.gpr .r9).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64
  stateBound : (stackArg s 1).toNat + 32 ≤ 2 ^ 64
  width : refillPLen s = pBytes
  valid : Spec.Dsa.generationPLenValid (refillPLen s)
  outLength : (s.gpr .rsi).toNat = 2 * refillPLen s + Spec.Dsa.generationQLen (refillPLen s)
  scratchLength : Spec.Dsa.generationScratchWords (refillPLen s) ≤ (stackArg s 0).toNat
  seeds : (s.mem.readW (stackArg s 1) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s))
  randLength : (s.gpr .r8).toNat ≤ Spec.Dsa.parameterEntropy (refillPLen s)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem refillABI_of {pBytes : Nat} {s : State} (h : (contract pBytes abi stackUse).pre s) :
    RefillABI pBytes s := by
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_split h
  constructor
  all_goals try simp only [inOut, inUsed, inRand, inScr, inState, inArgs]
  all_goals with_reducible assumption

/-! ## The frames

The stack below the return address, from `low = rsp - 568` up: the 192
octets the attempts' calls use, the attempts' frame of 296 (`refillBase`),
the controller's 32 and the saved registers' 48. -/

def low (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 stackUse

/-- The attempts' frame. -/
def refillBase (s : State) : Addr := off (low s) 192

/-- The controller's words. -/
def ctlRegion (F : Addr) : Region := ⟨off F 296, 32⟩

/-- The controller's `k`-th word. -/
def ctlWord (m : Mem) (F : Addr) (k : Nat) : BitVec 64 := m.readW (off F (296 + 8 * k)) 64

theorem low_toNat {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (low s).toNat = (s.gpr .rsp).toNat - stackUse := by
  have hl := h.stackLower
  simp only [low, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (s.gpr .rsp).isLt
  omega

theorem refillBase_toNat {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat = (s.gpr .rsp).toNat - 376 := by
  have hl : 568 ≤ (s.gpr .rsp).toNat := h.stackLower
  have hb := low_toNat h
  have := (s.gpr .rsp).isLt
  simp only [refillBase, off, BitVec.toNat_add, BitVec.toNat_ofNat, hb, stackUse, Nat.reducePow, Nat.reduceMod]
  omega

theorem low_sub {d n : Nat} (s : State) (h : d + n ≤ stackUse) :
    Region.Sub ⟨off (low s) d, n⟩ (below (s.gpr .rsp) stackUse) :=
  Offset.sub_base _ h

theorem refillBase_below (s : State) : below (refillBase s) 192 = ⟨low s, 192⟩ := by
  simp only [below, refillBase, off, BitVec.add_sub_cancel]

theorem ctlRegion_eq (s : State) : ctlRegion (refillBase s) = ⟨off (low s) 488, 32⟩ := by
  simp only [ctlRegion, refillBase, off_off]

/-- Regions of the stack below the return address are disjoint from the buffers. -/
theorem RefillABI.stack_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {d n : Nat}
    (hd : d + n ≤ stackUse) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s ∨ r = inArgs s) :
    (⟨off (low s) d, n⟩ : Region).Disjoint r := by
  have sub := low_sub s hd
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.stackOut.sub_left sub
  · exact h.stackUsed.sub_left sub
  · exact h.stackRand.sub_left sub
  · exact h.stackScr.sub_left sub
  · exact h.stackState.sub_left sub
  · exact h.stackArgs.sub_left sub

/-! ## The search's context -/

theorem RefillABI.lengths {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Spec.Dsa.generationLengthsValid pBytes (Spec.Dsa.generationQLen pBytes) := by
  have hv := h.valid
  rw [h.width] at hv
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
  rcases hv with (rfl | rfl) | rfl <;> decide

theorem RefillABI.scratchSize {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    VG.Impl.Dsa.Generation.Layout.usedBytes pBytes ≤ (stackArg s 0).toNat * 8 := by
  have hl := VG.Proof.Dsa.Generation.generation_layout_fits h.lengths
  have hs := h.scratchLength
  rw [h.width] at hs
  omega

theorem RefillABI.arena_sub {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Region.Sub ⟨s.gpr .r9, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ (inScr s) := by
  simpa [inScr] using (Offset.sub_base (s.gpr .r9) (d := 0) (by simpa using h.scratchSize))

def refillGeometry {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationGeometry where
  B := s.gpr .r9
  F := refillBase s
  pLen := pBytes
  qLen := Spec.Dsa.generationQLen pBytes
  lengths := h.lengths
  arenaBound := by have hb := h.scrBound; have hn := h.scratchSize; omega
  frameBound := by
    rw [refillBase_toNat h]; have hb := (s.gpr .rsp).isLt
    unfold VG.Impl.RsaOaep.X86_64.frameBytes; omega
  stackSize := by rw [refillBase_toNat h]; have hl : 568 ≤ (s.gpr .rsp).toNat := h.stackLower; omega
  frameArena := (h.stack_disjoint (d := 192) (n := 296) (by decide) (by simp)).sub_right h.arena_sub
  stackArena := by
    rw [refillBase_below]
    simpa only [off, BitVec.add_zero] using
      (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).sub_right h.arena_sub

/-- The random tape. -/
def randTape {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationTape (refillGeometry h) where
  ptr := s.gpr .rcx
  bytes := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
  bound := by rw [bytesAt_length]; exact h.randBound
  size := by rw [bytesAt_length]; exact (s.gpr .r8).isLt
  arena := by rw [bytesAt_length]; exact h.randScr.sub_right h.arena_sub
  frame := by
    rw [bytesAt_length]
    exact (h.stack_disjoint (r := inRand s) (d := 192) (n := 296) (by decide) (by simp)).symm
  stack := by
    rw [bytesAt_length]
    change (inRand s).Disjoint (below (refillBase s) 192)
    rw [refillBase_below]
    simpa only [off, BitVec.add_zero] using (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).symm

/-- The frame words the entry sets. -/
def refillWords (pBytes : Nat) (s : State) : Nat → BitVec 64
  | 3 => off (s.gpr .r9) VG.Impl.Dsa.Generation.Layout.wrappedSeed
  | 4 => off (s.gpr .r9) VG.Impl.Dsa.Generation.Layout.hashes
  | 5 => s.gpr .r9
  | 6 => s.gpr .rdi
  | 7 => s.gpr .rsi
  | 8 => s.gpr .rcx
  | 9 => s.gpr .r8
  | 11 => off (s.gpr .rcx) 0
  | 12 => 0
  | 13 => s.gpr .rcx
  | 15 => s.gpr .r8
  | 17 => BitVec.ofNat 64 pBytes
  | 18 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
  | 28 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
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
  hSlot := rfl
  hLengthSlot := by simp [refillWords, GenerationTape.slice]
  randSlot := rfl
  randLengthSlot := by simp [refillWords, randTape, bytesAt_length]
  pLenSlot := rfl
  qLenSlot := rfl
  hashLenSlot := rfl

theorem refillOutputPlan {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : OutputPlan (refillContext h) where
  lengthSlot := by
    change s.gpr .rsi = BitVec.ofNat 64 (2 * pBytes + Spec.Dsa.generationQLen pBytes)
    rw [← h.width, ← h.outLength]; simp
  bound := by
    change (s.gpr .rdi).toNat + (2 * pBytes + Spec.Dsa.generationQLen pBytes) ≤ 2 ^ 64
    rw [← h.width, ← h.outLength]; exact h.outBound
  separate := by
    intro r hr
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (⟨s.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r
    rw [← h.width, ← h.outLength]
    change (inOut s).Disjoint r
    rcases hr with rfl | rfl | rfl
    · exact h.outScr.sub_right h.arena_sub
    · exact (h.stack_disjoint (d := 192) (n := 296) (by decide) (by simp)).symm
    · change (inOut s).Disjoint (below (refillBase s) 192)
      rw [refillBase_below]
      simpa only [off, BitVec.add_zero] using (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).symm

end VG.Proof.Dsa.X86_64.Generation.Refill
