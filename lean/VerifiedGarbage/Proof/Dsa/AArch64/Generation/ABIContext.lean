module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABIGeometry
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.OutputPlan
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ToDual

/-! # Canonical persistent arguments obtained from the public ABI -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.AArch64

def abiWords (s : State) : Nat → BitVec 64
  | 3 => off (stackArg s 2) wrappedSeed
  | 4 => off (stackArg s 2) hashes
  | 5 => stackArg s 2
  | 6 => s.gpr .x0
  | 7 => s.gpr .x1
  | 8 => s.gpr .x4
  | 9 => s.gpr .x5
  | 11 => s.gpr .x6
  | 12 => off (stackArg s 2) VG.Impl.Dsa.Generation.Layout.hash
  | 13 => s.gpr .x7
  | 14 => stackArg s 0
  | 15 => stackArg s 1
  | 17 => s.gpr .x2
  | 18 => s.gpr .x3
  | 26 => s.gpr .x3
  | _ => 0

def contextOf {s : State} (h : GenerationABI s) : GenerationContext where
  geo := geometryOf h
  seeds := tapeOf h (s.gpr .x4) (s.gpr .x5) h.seedsBound h.seedsScratch h.stackSeeds
  hs := tapeOf h (s.gpr .x6) (s.gpr .x7) h.hsBound h.hsScratch h.stackHs
  rand := tapeOf h (stackArg s 0) (stackArg s 1) h.randBound h.randScratch h.stackRand
  saved := abiWords s
  wrappedSlot := rfl
  hashesSlot := rfl
  baseSlot := rfl
  seedsSlot := rfl
  seedsLengthSlot := by simp [abiWords, tapeOf, bytesAt_length]
  hSlot := rfl
  hLengthSlot := by simp [abiWords, tapeOf, bytesAt_length]
  randSlot := rfl
  randLengthSlot := by simp [abiWords, tapeOf, bytesAt_length]
  pLenSlot := by simp [abiWords, geometryOf]
  qLenSlot := by simp [abiWords, geometryOf]
  hashLenSlot := by simp [abiWords, geometryOf]

theorem outputPlanOf {s : State} (h : GenerationABI s) : OutputPlan (contextOf h) where
  lengthSlot := by change s.gpr .x1 = BitVec.ofNat 64 (2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat); rw [← h.outLength]; simp
  bound := by change (s.gpr .x0).toNat + (2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat) ≤ 2 ^ 64; rw [← h.outLength]; exact h.outBound
  separate := by
    intro r hr
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (⟨s.gpr .x0, 2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat⟩ : Region).Disjoint r
    rw [← h.outLength]
    rcases hr with rfl | rfl | rfl
    · exact h.outScratch.sub_right (generation_scratch_sub h)
    · exact (h.stackOut.sub_left (generation_frame_sub s)).symm
    · exact (h.stackOut.sub_left (generation_stack_sub s)).symm

end VG.Proof.Dsa.AArch64.Generation
