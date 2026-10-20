module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverGeometry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed


/-! # Resources supplied by the shared precomputed recovery signature -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure RecoverABI (s : State) : Prop where
  stackLow : recoverStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩, ⟨argAddr s 0, 52⟩]
  outputSource0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outputSource1 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  outputSource2 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  outputSource3 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  outputWorkspace : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  outputArguments : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  sourceWorkspace0 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  workspaceArguments : (⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  stackOutput : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  returnOutput : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  outputFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit0 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 11).toNat + 8 * (arg s 12).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eFits : (arg s 5).toNat ≤ (arg s 3).toNat
  hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat = some h ∧ (arg s 1).toNat = h.len
  space : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 10).toNat
  preLength : (arg s 12).toNat = Spec.Rsa.precomputedWords (arg s 3).toNat

theorem recoverABI_of {s : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) : RecoverABI s := by
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [recoverStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Sig.X86.Rcv
