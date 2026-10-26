module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIGeometry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputPlan
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import Mathlib.Tactic.ToDual

/-! # Canonical persistent arguments obtained from the public ABI -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.X86_64

def abiWords (s : State) : Nat → BitVec 64
  | 3 => off (stackArg s 4) wrappedSeed
  | 4 => off (stackArg s 4) hashes
  | 5 => stackArg s 4
  | 6 => s.gpr .rdi
  | 7 => s.gpr .rsi
  | 8 => s.gpr .r8
  | 9 => s.gpr .r9
  | 11 => stackArg s 0
  | 12 => stackArg s 1
  | 13 => stackArg s 2
  | 15 => stackArg s 3
  | 17 => s.gpr .rdx
  | 18 => s.gpr .rcx
  | 28 => s.gpr .rcx
  | _ => 0

def contextOf {s : State} (h : GenerationABI s) : GenerationContext where
  geo := geometryOf h
  seeds := tapeOf h (s.gpr .r8) (s.gpr .r9) h.seedsBound h.seedsScratch h.stackSeeds
  hs := tapeOf h (stackArg s 0) (stackArg s 1) h.hsBound h.hsScratch h.stackHs
  rand := tapeOf h (stackArg s 2) (stackArg s 3) h.randBound h.randScratch h.stackRand
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
  lengthSlot := by change s.gpr .rsi = BitVec.ofNat 64 (2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat); rw [← h.outLength]; simp
  bound := by change (s.gpr .rdi).toNat + (2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat) ≤ 2 ^ 64; rw [← h.outLength]; exact h.outBound
  separate := by
    intro r hr
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (⟨s.gpr .rdi, 2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat⟩ : Region).Disjoint r
    rw [← h.outLength]
    rcases hr with rfl | rfl | rfl
    · exact h.outScratch.sub_right (generation_scratch_sub h)
    · exact (h.stackOut.sub_left (generation_frame_sub s)).symm
    · exact (h.stackOut.sub_left (generation_stack_sub s)).symm

end VG.Proof.Dsa.X86_64.Generation
