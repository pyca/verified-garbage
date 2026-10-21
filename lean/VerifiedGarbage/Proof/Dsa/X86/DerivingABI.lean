module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Key-derivation resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure DerivingABI (s : State) : Prop where
  stackLow : 32 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 40 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 5, (arg s 6).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩, ⟨argAddr s 0, 36⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  keyOut : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  scalarOut : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  keyScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  scalarScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 7, (arg s 8).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowScalar : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat⟩
  keyBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  scalarBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratchBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 4).toNat (arg s 6).toNat
  keyLength : (arg s 3).toNat = 2 * (arg s 4).toNat + (arg s 6).toNat
  outLength : (arg s 1).toNat = 3 * (arg s 4).toNat + 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 4).toNat ≤ (arg s 8).toNat

theorem derivingABI_of {s : State} (h : (Spec.Dsa.deriveKeyContract abi 32).pre s) : DerivingABI s := by
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> first | with_reducible assumption | apply Region.Disjoint.symm; with_reducible assumption

end VG.Proof.Dsa.X86
