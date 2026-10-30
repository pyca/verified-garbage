module

public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit

/-! # Public parameter-generation ABI and its disjoint input buffers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

structure GenerationABI (s : State) : Prop where
  stackLower : 536 ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]
  outSeeds : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  outHs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  outRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  outArgs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  seedsScratch : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  hsScratch : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  randScratch : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  scratchArgs : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retSeeds : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  retHs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  stackOut : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  stackSeeds : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  stackHs : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  stackRand : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  stackScratch : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  stackArgs : (below (s.gpr .rsp) 536 : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  seedsBound : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  hsBound : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  randBound : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.generationLengthsValid (s.gpr .rdx).toNat (s.gpr .rcx).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (s.gpr .rdx).toNat + (s.gpr .rcx).toNat
  seedsLength : (s.gpr .r9).toNat % (s.gpr .rcx).toNat = 0
  hsLength : (stackArg s 1).toNat % (s.gpr .rdx).toNat = 0
  scratchLength : Spec.Dsa.generationScratchWords (s.gpr .rdx).toNat ≤ (stackArg s 5).toNat

theorem generationABI_of {s : State}
    (h : (Spec.Dsa.generateParametersContract abi 536).pre s) : GenerationABI s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six, List.range, List.range.loop] at h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six, List.range, List.range.loop] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86_64.Generation
