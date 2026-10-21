module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFrameResult
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
public import VerifiedGarbage.Spec.MillerRabin
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABISeparate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIValid

/-! # The complete native candidate satisfies the shared RSA generation contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 16)
    (roundVerified : Verified target round (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact 56))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 56)
    (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa (VG.Impl.RsaKeyGen.X86.Candidate.code montName mont roundName round) s trace t ∧
      abiPreserved s t ∧ contract.post s t := by
  have A := call_layout h
  have D := call_separation h
  obtain ⟨trace, t, run, preserved, R⟩ := framed_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    (call_valid h) (entry_input h) A.low D.returnFar
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, Spec.RsaKeyGen.candidateContract, Spec.RsaKeyGen.candidateSig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  have entropyLength : (callEntropy s).length = (arg s 8).toNat := VG.Proof.Bignum.bytesAt_length _ _ _
  change StepOutputs (callEnvironment s) (callEntropy s)
    (Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s)) t at R
  cases result : Spec.RsaKeyGen.candidateOp (arg s 1).toNat (callEBytes s) (callPBytes s) (callEntropy s) with
  | none =>
    rw [result] at R
    dsimp only [callEBytes, callPBytes, callEntropy] at result
    rw [result]
    obtain ⟨status, bytes, used⟩ := R
    refine ⟨by rw [status]; rfl, bytes, ?_⟩
    simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used
  | some pr =>
    obtain ⟨candidate, rest⟩ := pr
    rw [result] at R
    cases candidate
    all_goals dsimp only [StepOutputs, Outputs] at R
    all_goals obtain ⟨status, bytes, used⟩ := R
    all_goals rw [entropyLength] at used
    all_goals dsimp only [callEBytes, callPBytes, callEntropy] at result
    all_goals rw [result]
    all_goals refine ⟨by rw [status]; rfl, bytes, ?_⟩
    all_goals simpa only [callEnvironment, Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.map_append, List.map_nil,
      List.map_cons, List.nil_append, Nat.mul_zero, BitVec.add_zero] using congrArg (fun x => [x]) used

end VG.Proof.RsaKeyGen.X86.Candidate
