module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Domain-checking resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure CheckingABI (s : State) : Prop where
  stackLow : 108 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  keyScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  keyBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 2).toNat (arg s 3).toNat
  keyLength : (arg s 1).toNat = 2 * (arg s 2).toNat + (arg s 3).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 2).toNat ≤ (arg s 5).toNat

theorem checkingABI_of {s : State} (h : (Proof.Dsa.checkParametersContract abi 108).pre s) : CheckingABI s := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86
