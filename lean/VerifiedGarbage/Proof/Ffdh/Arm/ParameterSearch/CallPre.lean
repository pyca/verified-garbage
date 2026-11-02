module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ArgumentWords
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallFacts
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! The nested native candidate satisfies the existing public FFDH signature's precondition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem call_pre {p : SearchParams} {used : Nat} {s : State} {m : Mem}
    (facts : CallFacts p used s.sp) (context : ArgumentContext p used s)
    (memory : s.mem = callMem p used m s.sp) (room : used + p.c.length ≤ p.c.bytes.length) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre (callState p used s) := by
  let q := p.candidateParams used room
  have a0 := call_stackArg (j := 0) facts.argsFits memory (by decide)
  have a1 := call_stackArg (j := 1) facts.argsFits memory (by decide)
  have a2 := call_stackArg (j := 2) facts.argsFits memory (by decide)
  have a3 := call_stackArg (j := 3) facts.argsFits memory (by decide)
  have a4 := call_stackArg (j := 4) facts.argsFits memory (by decide)
  simp only [callValue] at a0 a1 a2 a3 a4
  have widthNat : (BitVec.ofNat 32 p.c.length).toNat = p.c.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega)]
  have bitsNat : (BitVec.ofNat 32 p.c.bits).toNat = p.c.bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.maxBits; omega)]
  have genNat : (BitVec.ofNat 32 p.c.generator).toNat = p.c.generator := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.c.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (BitVec.ofNat 32 (p.c.bytes.length - used)).toNat = p.c.bytes.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.tapeCount; omega)]
  have capNat : (BitVec.ofNat 32 p.c.capacity).toNat = p.c.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.capacity_fits]
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [context.out, context.width, context.usedPtr, context.bits,
    a0, a1, a2, a3, a4, widthNat, bitsNat, genNat, tapeNat, capNat]
  have argAddr : stackArgAddr (callState p used s) 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr]
  simp only [Nat.mul_comm p.c.capacity 8]
  have address := FrameStack.addr_sub' facts.stackFits
  change BitVec.setWidth 64 (s.sp - 184#32) = BitVec.setWidth 64 s.sp - 184#64 at address
  rw [← address]
  refine ⟨facts.stackFits, facts.argsFits, rfl, rfl, q.outputUsed, ?_, q.outputScratch,
    facts.outputArgs, ?_, q.usedScratch, facts.usedArgs, ?_, facts.scratchArgs,
    facts.stackOutput, facts.stackUsed, facts.stackTape, facts.stackScratch, facts.stackArgs,
    q.outputFits, q.usedFits, ?_, q.scratchFits, p.c.minBits, p.c.maxBits, rfl, p.c.generatorAllowed, p.c.space⟩
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.outputTape
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.usedTape
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.tapeScratch
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.tapeFits

end VG.Proof.Ffdh.Arm.ParameterSearch
