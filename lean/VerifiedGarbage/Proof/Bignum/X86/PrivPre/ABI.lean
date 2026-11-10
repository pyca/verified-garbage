module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute

/-! # `vg_rsa_private_precompute` on x86: its resources

What the contract (`Spec.Rsa.privatePrecomputeContract abi stackBytes`)
gives: the permissions, the buffers apart, their lengths (`PPABI`,
`ppABI_of`). The arguments: `pre` (0) and its words (1), `n` (2) and its
bytes (3), `p` (4, 5), `q` (6, 7), the working space (8) and its words (9).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

/-- The frame (96 bytes) and the largest callee's stack (96) and return address. -/
def stackBytes : Nat := 196

structure PPABI (s : State) : Prop where
  stackLow : stackBytes ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 40 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩,
    ⟨argumentPointer s 6, (arg s 7).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat * 8⟩, ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩,
    ⟨argAddr s 0, 40⟩]
  preN : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  preP : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  preQ : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  preWs : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  preArgs : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  nWs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  nArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  pWs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  pArgs : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  qWs : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  qArgs : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  wsArgs : (⟨argumentPointer s 8, (arg s 9).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  retPre : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  retN : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retP : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  retQ : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 6, (arg s 7).toNat⟩
  retWs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩
  belowPre : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  belowN : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowP : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat⟩
  belowQ : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 6, (arg s 7).toNat⟩
  belowWs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨argAddr s 0, 40⟩
  preBound : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  pBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  qBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  wsBound : (arg s 8).toNat + (arg s 9).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  pPositive : 1 ≤ (arg s 5).toNat
  pLength : (arg s 5).toNat < (arg s 3).toNat
  qPositive : 1 ≤ (arg s 7).toNat
  qLength : (arg s 7).toNat < (arg s 3).toNat
  preLength : (arg s 1).toNat = Spec.Rsa.privatePrecomputedWords (arg s 3).toNat (arg s 5).toNat (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 3).toNat ≤ (arg s 9).toNat

theorem ppABI_of {s : State} (h : (Spec.Rsa.privatePrecomputeContract abi stackBytes).pre s) : PPABI s := by
  sig_pre [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argSlots, argVal, argBytes,
    stackBelow, stackBytes] at h
  sig_split h
  constructor <;> (try simp only [stackBytes]) <;> with_reducible assumption

end VG.Proof.Bignum.X86.PrivPre
