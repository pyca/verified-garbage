module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Caller resources for public RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure PrecomputeABI (s : State) : Prop where
  stackLow : 20 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat * 8⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  preLength : (arg s 1).toNat = Spec.Rsa.precomputedWords (arg s 3).toNat
  scratchLength : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 5).toNat

theorem precomputeABI_of {s : State} (h : (Spec.Rsa.publicPrecomputeContract abi 20).pre s) : PrecomputeABI s := by
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Bignum.X86
