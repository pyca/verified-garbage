module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContractGeometry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract

/-! # Resources provided by the shared private RSA contract on i686 -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure SignABI (s : State) : Prop where
  stackLow : sigStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 88 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 9, (arg s 10).toNat⟩, ⟨argumentPointer s 11, (arg s 12).toNat⟩, ⟨argumentPointer s 13, (arg s 14).toNat⟩, ⟨argumentPointer s 15, (arg s 16).toNat⟩, ⟨argumentPointer s 17, (arg s 18).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩, ⟨argAddr s 0, 84⟩]
  outN : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outE : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  outI : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  outP : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat⟩
  outQ : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat⟩
  outDP : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 13, (arg s 14).toNat⟩
  outDQ : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 15, (arg s 16).toNat⟩
  outQI : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 17, (arg s 18).toNat⟩
  outWs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 84⟩
  nWs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  eWs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  iWs : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  pWs : (⟨argumentPointer s 9, (arg s 10).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  qWs : (⟨argumentPointer s 11, (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  dpWs : (⟨argumentPointer s 13, (arg s 14).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  dqWs : (⟨argumentPointer s 15, (arg s 16).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  qiWs : (⟨argumentPointer s 17, (arg s 18).toNat⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  wsArgs : (⟨argumentPointer s 19, (arg s 20).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 84⟩
  stackOut : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackN : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackE : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  stackI : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackP : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 9, (arg s 10).toNat⟩
  stackQ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 11, (arg s 12).toNat⟩
  stackDP : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 13, (arg s 14).toNat⟩
  stackDQ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 15, (arg s 16).toNat⟩
  stackQI : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 17, (arg s 18).toNat⟩
  stackWs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  stackArgs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨argAddr s 0, 84⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  retWs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 19, (arg s 20).toNat * 8⟩
  outFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  nFit : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  eFit : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  iFit : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  pFit : (arg s 9).toNat + (arg s 10).toNat ≤ 2 ^ 32
  qFit : (arg s 11).toNat + (arg s 12).toNat ≤ 2 ^ 32
  dpFit : (arg s 13).toNat + (arg s 14).toNat ≤ 2 ^ 32
  dqFit : (arg s 15).toNat + (arg s 16).toNat ≤ 2 ^ 32
  qiFit : (arg s 17).toNat + (arg s 18).toNat ≤ 2 ^ 32
  wsFit : (arg s 19).toNat + (arg s 20).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eFits : (arg s 5).toNat ≤ (arg s 3).toNat
  pPositive : 1 ≤ (arg s 10).toNat
  pShort : (arg s 10).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 12).toNat
  qShort : (arg s 12).toNat < (arg s 3).toNat
  dpLen : (arg s 14).toNat = (arg s 10).toNat
  qiLen : (arg s 18).toNat = (arg s 10).toNat
  dqLen : (arg s 16).toNat = (arg s 12).toNat
  space : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 20).toNat

theorem signABI_of {s : State} (h : (Spec.RsaPkcs1Sig.signContract abi sigStack).pre s) : SignABI s := by
  sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [sigStack] at * <;> with_reducible assumption
end VG.Proof.RsaPkcs1Sig.X86.Sgn
