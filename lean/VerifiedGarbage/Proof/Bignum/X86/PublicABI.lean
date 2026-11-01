module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Public RSA resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure PublicABI (s : State) : Prop where
  stackLow : 20 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩,
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩, ⟨argAddr s 0, 40⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  eScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  inScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 8, (arg s 9).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  eBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  inBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  scratchBound : (arg s 8).toNat + (arg s 9).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 7).toNat = (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eLength : (arg s 5).toNat ≤ (arg s 3).toNat
  scratchLength : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 9).toNat

theorem publicABI_of {s : State} (h : (Proof.Rsa.publicCheckedContract abi 20).pre s) : PublicABI s := by
  sig_pre [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Bignum.X86
