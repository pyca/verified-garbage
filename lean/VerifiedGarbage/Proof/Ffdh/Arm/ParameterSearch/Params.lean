module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Spec.Ffdh.Generation

/-! Public inputs for the native parameter retry/refill controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

structure SearchParams where
  candidate : VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
  control : BitVec 32
  attempts : Nat
  attemptsBound : attempts ≤ Spec.Ffdh.parameterAttempts candidate.bits
  tapeBound : candidate.bytes.length ≤ Spec.Ffdh.parameterEntropy candidate.bits
  controlFits : control.toNat + 128 ≤ 2 ^ 32
  controlOutput : (⟨State.addr control, 128⟩ : Region).Disjoint ⟨State.addr candidate.out, candidate.length⟩
  controlUsed : (⟨State.addr control, 128⟩ : Region).Disjoint ⟨State.addr candidate.usedPtr, 8⟩
  controlScratch : (⟨State.addr control, 128⟩ : Region).Disjoint ⟨State.addr candidate.base, 8 * candidate.capacity⟩
  controlTape : (⟨State.addr control, 128⟩ : Region).Disjoint ⟨State.addr candidate.tape, candidate.bytes.length⟩

abbrev SearchParams.c (p : SearchParams) := p.candidate

def SearchParams.tail (p : SearchParams) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  (Spec.Ffdh.parameterSearch p.c.bits p.c.generator remaining (p.c.bytes.drop used)).consume used

def searchValues (p : SearchParams) (used : Nat) : Nat → BitVec 32
  | 1 => BitVec.ofNat 32 p.c.length
  | 2 => BitVec.ofNat 32 (Spec.Ffdh.parameterEntropy p.c.bits)
  | 4 => BitVec.ofNat 32 used
  | 5 => p.c.out
  | 6 => p.c.usedPtr
  | 7 => BitVec.ofNat 32 p.c.bits
  | 8 => BitVec.ofNat 32 p.c.generator
  | 9 => p.c.tape + BitVec.ofNat 32 used
  | 10 => BitVec.ofNat 32 (p.c.bytes.length - used)
  | 11 => p.c.base
  | 12 => BitVec.ofNat 32 p.c.capacity
  | _ => 0

def searchSlots : List Nat := [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def searchRegions (p : SearchParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr p.c.base, 8 * p.c.capacity⟩,
    ⟨State.addr p.control, 128⟩, FrameStack.belowA sp 208]

end VG.Proof.Ffdh.Arm.ParameterSearch
