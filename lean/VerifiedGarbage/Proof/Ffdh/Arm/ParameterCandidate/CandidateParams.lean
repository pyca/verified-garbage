module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Spec.Rsa.Contract

/-! Public candidate arguments and buffer bounds from the existing FFDH contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

structure CandidateParams where
  out : BitVec 32
  usedPtr : BitVec 32
  tape : BitVec 32
  base : BitVec 32
  bits : Nat
  generator : Nat
  capacity : Nat
  bytes : List Byte
  minBits : 512 ≤ bits
  maxBits : bits ≤ 8192
  generatorAllowed : generator = 2 ∨ generator = 5
  space : Spec.Rsa.scratchWords ((bits + 7) / 8) ≤ capacity
  scratchFits : base.toNat + 8 * capacity ≤ 2 ^ 32
  outputFits : out.toNat + (bits + 7) / 8 ≤ 2 ^ 32
  usedFits : usedPtr.toNat + 8 ≤ 2 ^ 32
  tapeFits : tape.toNat + bytes.length ≤ 2 ^ 32
  tapeCount : bytes.length < 2 ^ 32
  outputUsed : (⟨State.addr out, (bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr usedPtr, 8⟩
  outputScratch : (⟨State.addr out, (bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  outputTape : (⟨State.addr out, (bits + 7) / 8⟩ : Region).Disjoint ⟨State.addr tape, bytes.length⟩
  usedScratch : (⟨State.addr usedPtr, 8⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩
  usedTape : (⟨State.addr usedPtr, 8⟩ : Region).Disjoint ⟨State.addr tape, bytes.length⟩
  tapeScratch : (⟨State.addr tape, bytes.length⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩

def CandidateParams.length (p : CandidateParams) : Nat := (p.bits + 7) / 8

def CandidateParams.words (p : CandidateParams) : Nat := Spec.Rsa.modulusWords p.length

def CandidateParams.candidate (p : CandidateParams) : Nat :=
  Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.bytes.take p.length))

def candidateValues (p : CandidateParams) (consumed : Nat) : Nat → BitVec 32
  | 0 => p.base
  | 4 => p.out
  | 8 => p.out
  | 12 => BitVec.ofNat 32 p.length
  | 16 => p.tape
  | 20 => BitVec.ofNat 32 p.bytes.length
  | 24 => BitVec.ofNat 32 p.bits
  | 28 => BitVec.ofNat 32 p.generator
  | 32 => p.usedPtr
  | 36 => BitVec.ofNat 32 p.capacity
  | 40 => BitVec.ofNat 32 consumed
  | _ => 0

def candidateSlots : List Nat := [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40]

def candidateRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.out, p.length⟩, ⟨State.addr p.base, 8 * p.capacity⟩,
    FrameStack.belowA sp 56, ⟨State.addr (sp + 40#32), 28⟩]

structure CandidateContext (p : CandidateParams) (consumed : Nat) (s : State) : Prop where
  saved : SavedFrame (candidateValues p consumed) candidateSlots s
  workspace : VG.Proof.Bignum.Arm.Workspace s p.base (8 * p.capacity)
  outputWrite : InRegions s.wr (State.addr p.out) p.length
  usedWrite : InRegions s.wr (State.addr p.usedPtr) 8
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes
  consumedBound : consumed ≤ p.bytes.length
  stackBelow : 56 ≤ s.sp.toNat
  stackOutput : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.out, p.length⟩
  stackUsed : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.usedPtr, 8⟩
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackTape : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.tape, p.bytes.length⟩
  belowOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.out, p.length⟩
  belowUsed : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.usedPtr, 8⟩
  belowScratch : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  belowTape : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.tape, p.bytes.length⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
