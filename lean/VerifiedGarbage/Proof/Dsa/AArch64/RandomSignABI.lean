module

public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! The randomized-signing ABI, including the wrapper and callee stack allowance. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64

theorem randomSignStackArgs (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure RandomSignABI (extra : Nat) (s : State) : Prop where
  stackLower : extra + 256 ≤ (s.sp).toNat
  stackUpper : s.sp.toNat + 40 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨s.gpr .x7, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨s.gpr .x2, 8⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outUsed : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x2, 8⟩
  outKey : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  outDigest : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  outRand : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  outScratch : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  outArgs : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  usedKey : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  usedDigest : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  usedRand : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  usedScratch : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  usedArgs : (⟨s.gpr .x2, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  keyScratch : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  digestScratch : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  randScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  stackOut : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
  stackUsed : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x2, 8⟩
  stackKey : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  stackDigest : (below (s.sp) (extra + 256)).Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩
  stackRand : (below (s.sp) (extra + 256)).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  stackScratch : (below (s.sp) (extra + 256)).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  stackArgs : (below (s.sp) (extra + 256)).Disjoint ⟨stackArgAddr s 0, 40⟩
  outBound : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).base.toNat + (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).len ≤ 2 ^ 64
  usedBound : (⟨s.gpr .x2, 8⟩ : Region).base.toNat + (⟨s.gpr .x2, 8⟩ : Region).len ≤ 2 ^ 64
  keyBound : (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).base.toNat + (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).len ≤ 2 ^ 64
  digestBound : (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).base.toNat + (⟨s.gpr .x7, (stackArg s 0).toNat⟩ : Region).len ≤ 2 ^ 64
  randBound : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).base.toNat + (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).len ≤ 2 ^ 64
  scratchBound : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).base.toNat + (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).len ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .x5).toNat (s.gpr .x6).toNat
  outLength : (s.gpr .x1).toNat = 2 * (s.gpr .x6).toNat
  keyLength : (s.gpr .x4).toNat = 3 * (s.gpr .x5).toNat + 2 * (s.gpr .x6).toNat
  scratchLength : Spec.Dsa.randomSignScratchWords (s.gpr .x5).toNat ≤ (stackArg s 4).toNat

theorem randomSignABI_of {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignContract abi (extra + 256)).pre s) : RandomSignABI extra s := by
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.AArch64
