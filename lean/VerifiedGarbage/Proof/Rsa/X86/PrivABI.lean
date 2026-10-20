module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.TCB.X86.Target


/-! # Resources provided by the shared private RSA contract on i686 -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure PrivABI (s : State) : Prop where
  stackLow : stackBytes ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 84 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩, ⟨argumentPointer s 8, (arg s 9).toNat⟩, ⟨argumentPointer s 10, (arg s 11).toNat⟩, ⟨argumentPointer s 12, (arg s 13).toNat⟩, ⟨argumentPointer s 14, (arg s 15).toNat⟩, ⟨argumentPointer s 16, (arg s 17).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩, ⟨argAddr s 0, 80⟩]
  outN : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outE : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  outI : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  outP : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat⟩
  outQ : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, (arg s 11).toNat⟩
  outDP : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 12, (arg s 13).toNat⟩
  outDQ : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 14, (arg s 15).toNat⟩
  outQI : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat⟩
  outWs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  nWs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  eWs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  iWs : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  pWs : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  qWs : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  dpWs : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  dqWs : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  qiWs : (⟨argumentPointer s 16, (arg s 17).toNat⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  wsArgs : (⟨argumentPointer s 18, (arg s 19).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  stackOut : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackN : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackE : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  stackI : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  stackP : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat⟩
  stackQ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 10, (arg s 11).toNat⟩
  stackDP : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 12, (arg s 13).toNat⟩
  stackDQ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 14, (arg s 15).toNat⟩
  stackQI : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat⟩
  stackWs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  stackArgs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨argAddr s 0, 80⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retWs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 18, (arg s 19).toNat * 8⟩
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nFit : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  eFit : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  iFit : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  pFit : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  qFit : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dpFit : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  dqFit : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  qiFit : (arg s 16).toNat + (arg s 17).toNat ≤ 2 ^ 32
  wsFit : (arg s 18).toNat + (arg s 19).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 3).toNat
  inputLen : (arg s 7).toNat = (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eFits : (arg s 5).toNat ≤ (arg s 3).toNat
  pPositive : 1 ≤ (arg s 9).toNat
  pShort : (arg s 9).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 11).toNat
  qShort : (arg s 11).toNat < (arg s 3).toNat
  dpLen : (arg s 13).toNat = (arg s 9).toNat
  qiLen : (arg s 17).toNat = (arg s 9).toNat
  dqLen : (arg s 15).toNat = (arg s 11).toNat
  space : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 19).toNat

theorem privateABI_of {s : State} (h : (Spec.Rsa.privateCheckedContract abi stackBytes).pre s) : PrivABI s := by
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [stackBytes] at * <;> with_reducible assumption
end VG.Proof.Rsa.X86.PrivChecked
