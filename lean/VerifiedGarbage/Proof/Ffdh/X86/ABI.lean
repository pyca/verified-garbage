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

end VG.Proof.Ffdh.X86
