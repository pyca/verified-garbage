module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePost
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! The complete ARMv7 candidate callable satisfies the existing shared FFDH contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_correct (v : RoundImpl) (s : State)
    (pre : (Spec.Ffdh.sievedParameterCandidateContract abi 184).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) s tr t ∧
      abiPreserved s t ∧ (Spec.Ffdh.sievedParameterCandidateContract abi 184).post s t := by
  obtain ⟨p, args⟩ := candidatePublic s pre
  obtain ⟨tr, t, run, preserved, post⟩ := candidateFn_ok v (candidateInput pre args)
  refine ⟨tr, t, run, preserved, ?_⟩
  have result := candidatePost_spec post
  have widthNat : (s.gpr .r1).toNat = p.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.length_bounds; omega)]
  have bitsNat : (s.gpr .r3).toNat = p.bits := by
    rw [args.bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.maxBits; omega)]
  have generatorNat : (stackArg s 0).toNat = p.generator := by
    rw [args.generator, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (stackArg s 2).toNat = p.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount]
  have bytes := args.bytes
  simp only [State.addr] at bytes result
  sig_post [Spec.Ffdh.sievedParameterCandidateContract, Spec.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [args.out, args.used, args.tape, widthNat, bitsNat, generatorNat, tapeNat, bytes]
  exact result

end VG.Proof.Ffdh.Arm.ParameterCandidate
