module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # Public parameter-generation ABI and its disjoint input buffers -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem generationStackArgs (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

structure GenerationABI (s : State) : Prop where
  stackLower : 464 ≤ (s.sp).toNat
  stackUpper : (s.sp).toNat + 32 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, (s.gpr .x7).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArgAddr s 0, 32⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩]
  outSeeds : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  outHs : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  outRand : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  outArgs : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  seedsScratch : (⟨s.gpr .x4, (s.gpr .x5).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  hsScratch : (⟨s.gpr .x6, (s.gpr .x7).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  randScratch : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  scratchArgs : (⟨stackArg s 2, (stackArg s 3).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  stackOut : (below (s.sp) 464 : Region).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  stackSeeds : (below (s.sp) 464 : Region).Disjoint ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
  stackHs : (below (s.sp) 464 : Region).Disjoint ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
  stackRand : (below (s.sp) 464 : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  stackScratch : (below (s.sp) 464 : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
  stackArgs : (below (s.sp) 464 : Region).Disjoint ⟨stackArgAddr s 0, 32⟩
  outBound : (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64
  seedsBound : (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64
  hsBound : (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64
  randBound : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.generationLengthsValid (s.gpr .x2).toNat (s.gpr .x3).toNat
  outLength : (s.gpr .x1).toNat = 2 * (s.gpr .x2).toNat + (s.gpr .x3).toNat
  seedsLength : (s.gpr .x5).toNat % (s.gpr .x3).toNat = 0
  hsLength : (s.gpr .x7).toNat % (s.gpr .x2).toNat = 0
  scratchLength : Spec.Dsa.generationScratchWords (s.gpr .x2).toNat ≤ (stackArg s 3).toNat

theorem generationABI_of {s : State}
    (h : (Spec.Dsa.generateParametersContract abi 464).pre s) : GenerationABI s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, generationStackArgs,
    show 464 = 463 + 1 from rfl] at h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, generationStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64.Generation
