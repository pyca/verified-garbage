module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI

/-! # Signing resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86

structure SigningABI (s : State) : Prop where
  stackLow : 32 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 48 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩, ⟨argAddr s 0, 44⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  keyScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  nonceScratch : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  digestScratch : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 9, (arg s 10).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 44⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 9, (arg s 10).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowNonce : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat⟩
  belowDigest : (⟨(s.gpr .esp).setWidth 64 - 32#64, 32⟩ : Region).Disjoint
    ⟨argumentPointer s 7, (arg s 8).toNat⟩
  keyBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  nonceBound : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  digestBound : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  scratchBound : (arg s 9).toNat + (arg s 10).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 4).toNat (arg s 6).toNat
  keyLength : (arg s 3).toNat = 3 * (arg s 4).toNat + 2 * (arg s 6).toNat
  outLength : (arg s 1).toNat = 2 * (arg s 6).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 4).toNat ≤ (arg s 10).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi 32).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Dsa.X86
