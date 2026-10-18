module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptContractGeometry

/-! # Resources supplied by the shared precomputed-encryption signature -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure EncryptABI (s : State) : Prop where
  stackLow : encryptStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 60 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 6, (arg s 7).toNat⟩, ⟨argumentPointer s 8, (arg s 9).toNat⟩, ⟨argumentPointer s 12, 8 * (arg s 13).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩, ⟨argAddr s 0, 56⟩]
  outputSource0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outputSource1 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  outputSource2 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  outputSource3 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat⟩
  outputSource4 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 12, 8 * (arg s 13).toNat⟩
  outputWorkspace : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  outputArguments : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 56⟩
  sourceWorkspace0 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  sourceWorkspace4 : (⟨argumentPointer s 12, 8 * (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  workspaceArguments : (⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 56⟩
  stackOutput : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat⟩
  stackSource4 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 12, 8 * (arg s 13).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 encryptStack, encryptStack⟩ : Region).Disjoint ⟨argAddr s 0, 56⟩
  returnOutput : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 10, 8 * (arg s 11).toNat⟩
  outputFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit0 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  sourceFit4 : (arg s 12).toNat + 8 * (arg s 13).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 10).toNat + 8 * (arg s 11).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 3).toNat
  outLen : (arg s 1).toNat = (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eFits : (arg s 5).toNat ≤ (arg s 3).toNat
  messageFits : (arg s 7).toNat + 11 ≤ (arg s 3).toNat
  padding : (arg s 9).toNat = (arg s 3).toNat - (arg s 7).toNat - 3
  space : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 11).toNat
  preLength : (arg s 13).toNat = Spec.Rsa.precomputedWords (arg s 3).toNat

theorem encryptABI_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptPrecomputedContract abi encryptStack).pre s) : EncryptABI s := by
  sig_pre [Spec.RsaPkcs1Enc.encryptPrecomputedContract, Spec.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [encryptStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Enc.X86.Enc
