module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.Sig

/-! # FFDH on i686: the resources the cdecl contracts supply -/

@[expose] public section
namespace VG.Proof.Ffdh.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The bytes of stack the functions use: the frame of the synthetic arguments, a call's frame and its
return address. -/
abbrev stack : Nat := 116

structure CheckDomainABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 3, (arg s 4).toNat * 8⟩, ⟨argAddr s 0, 20⟩]
  domScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 3, (arg s 4).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 3, (arg s 4).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 20⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 3, (arg s 4).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint
    ⟨argumentPointer s 3, (arg s 4).toNat * 8⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  domBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  scratchBound : (arg s 3).toNat + (arg s 4).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 2).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 2).toNat (arg s 1).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 2).toNat ≤ (arg s 4).toNat

theorem checkDomainABI_of {s : State} (h : (Spec.Ffdh.checkDomainContract abi stack).pre s) : CheckDomainABI s := by
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

structure CheckPublicABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 3, (arg s 4).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 5, (arg s 6).toNat * 8⟩, ⟨argAddr s 0, 28⟩]
  domScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  domArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  yScratch : (⟨argumentPointer s 3, (arg s 4).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  yArgs : (⟨argumentPointer s 3, (arg s 4).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  scratchArgs : (⟨argumentPointer s 5, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retY : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 3, (arg s 4).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 3, (arg s 4).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  domBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  scratchBound : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 2).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 2).toNat (arg s 1).toNat
  yLen : (arg s 4).toNat = (arg s 2).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 2).toNat ≤ (arg s 6).toNat

theorem checkPublicABI_of {s : State} (h : (Spec.Ffdh.checkPublicContract abi stack).pre s) : CheckPublicABI s := by
  sig_pre [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

structure CheckPrivateABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 36 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 3, (arg s 4).toNat⟩,
    ⟨argumentPointer s 5, (arg s 6).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 7, (arg s 8).toNat * 8⟩, ⟨argAddr s 0, 36⟩]
  domScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  yScratch : (⟨argumentPointer s 3, (arg s 4).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  xScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 7, (arg s 8).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 36⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 3, (arg s 4).toNat⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat * 8⟩
  domBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  yBound : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  xBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  scratchBound : (arg s 7).toNat + (arg s 8).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 2).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 2).toNat (arg s 1).toNat
  yLen : (arg s 4).toNat = (arg s 2).toNat
  xPos : 1 ≤ (arg s 6).toNat
  xLen : (arg s 6).toNat ≤ (arg s 2).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 2).toNat ≤ (arg s 8).toNat

theorem checkPrivateABI_of {s : State} (h : (Spec.Ffdh.checkPrivateContract abi stack).pre s) :
    CheckPrivateABI s := by
  sig_pre [Spec.Ffdh.checkPrivateContract, Spec.Ffdh.checkPrivateSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

structure ExchangeABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 44 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩,
    ⟨argumentPointer s 7, (arg s 8).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩,
    ⟨argAddr s 0, 44⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  domScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  xScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  yScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  outDom : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outX : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  outY : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowOut : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowX : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowY : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 116#64, 116⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  domBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  xBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  yBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 4).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 4).toNat (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 4).toNat
  yLen : (arg s 8).toNat = (arg s 4).toNat
  xPos : 1 ≤ (arg s 6).toNat
  xLen : (arg s 6).toNat ≤ (arg s 4).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 4).toNat ≤ (arg s 10).toNat

theorem exchangeABI_of {s : State} (h : (Spec.Ffdh.exchangeContract abi stack).pre s) : ExchangeABI s := by
  sig_pre [Spec.Ffdh.exchangeContract, Spec.Ffdh.exchangeSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Ffdh.X86
