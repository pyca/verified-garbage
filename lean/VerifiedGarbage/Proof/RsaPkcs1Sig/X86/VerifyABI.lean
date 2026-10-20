module
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyGeometry
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed


/-! # Resources supplied by the shared precomputed-verification signature -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure VerifyABI (s : State) : Prop where
  stackLow : verifyStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩, ⟨argAddr s 0, 52⟩]
  sourceWorkspace0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace4 : (⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  workspaceArguments : (⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackSource4 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceFit0 : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  sourceFit4 : (arg s 11).toNat + 8 * (arg s 12).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 1).toNat
  ePositive : 1 ≤ (arg s 3).toNat
  eFits : (arg s 3).toNat ≤ (arg s 1).toNat
  space : Spec.Rsa.publicScratchWords (arg s 1).toNat ≤ (arg s 10).toNat
  preLength : (arg s 12).toNat = Spec.Rsa.precomputedWords (arg s 1).toNat

theorem verifyABI_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) : VerifyABI s := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [verifyStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Sig.X86.Ver
