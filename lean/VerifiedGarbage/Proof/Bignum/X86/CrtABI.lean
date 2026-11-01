module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Private CRT RSA resources supplied by the shared cdecl contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure CrtABI (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat⟩,
    ⟨argumentPointer s 6, (arg s 7).toNat⟩,
    ⟨argumentPointer s 8, (arg s 9).toNat⟩,
    ⟨argumentPointer s 10, (arg s 11).toNat⟩,
    ⟨argumentPointer s 12, (arg s 13).toNat⟩,
    ⟨argumentPointer s 14, (arg s 15).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩,
    ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, ⟨argAddr s 0, 72⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  inScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  pScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qScratch : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dpScratch : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dqScratch : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qiScratch : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 72⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  inBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  pBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  qBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  dpBound : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dqBound : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  qiBound : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  scratchBound : (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 5).toNat = (arg s 3).toNat
  pPositive : 1 ≤ (arg s 7).toNat
  pLength : (arg s 7).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 9).toNat
  qLength : (arg s 9).toNat < (arg s 3).toNat
  dpLength : (arg s 11).toNat = (arg s 7).toNat
  qiLength : (arg s 15).toNat = (arg s 7).toNat
  dqLength : (arg s 13).toNat = (arg s 9).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 17).toNat

theorem crtABI_of {s : State} (h : (Proof.Rsa.privateCrtContract abi 96).pre s) : CrtABI s := by
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Bignum.X86
