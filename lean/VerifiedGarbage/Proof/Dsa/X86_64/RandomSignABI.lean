module

public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.X86_64.Call
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! The randomized-signing ABI, including the wrapper and callee stack allowance. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64

theorem stackArgs_seven (s : State) : List.map (stackArg s) (List.range 7) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6] := rfl

structure RandomSignABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 64 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArgAddr s 0, 56⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩]
  outUsed : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  outKey : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  outDigest : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  outRand : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  outArgs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  usedKey : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  usedDigest : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  usedRand : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  usedScratch : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  usedArgs : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  keyScratch : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  digestScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  randScratch : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  scratchArgs : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  stackOut : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  stackUsed : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rdx, 8⟩
  retKey : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  stackKey : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  retDigest : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  stackDigest : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  stackRand : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  stackScratch : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 56⟩
  stackArgs : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 56⟩
  outBound : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).base.toNat + (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).len ≤ 2 ^ 64
  usedBound : (⟨s.gpr .rdx, 8⟩ : Region).base.toNat + (⟨s.gpr .rdx, 8⟩ : Region).len ≤ 2 ^ 64
  keyBound : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).base.toNat + (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).len ≤ 2 ^ 64
  digestBound : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).base.toNat + (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).len ≤ 2 ^ 64
  randBound : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).base.toNat + (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).len ≤ 2 ^ 64
  scratchBound : (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).base.toNat + (⟨stackArg s 5, (stackArg s 6).toNat * 8⟩ : Region).len ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r9).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (stackArg s 0).toNat
  keyLength : (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat + 2 * (stackArg s 0).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (s.gpr .r9).toNat ≤ (stackArg s 6).toNat

theorem randomSignABI_of {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignContract abi (extra + 256)).pre s) : RandomSignABI extra s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86_64
