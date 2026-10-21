module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateContractCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSat
import VerifiedGarbage.Proof.Ffdh.Arm.CallerRows
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! Complete native ARMv7 parameter candidates satisfy the shared public API. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_verified (v : RoundImpl) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code)
      (Spec.Ffdh.sievedParameterCandidateContract abi 184) :=
  ⟨candidate_correct v, candidate_contract_ct v, candidate_sat⟩

theorem optimizedCandidate_verified (umaal : Bool) (v : RoundImpl) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode umaal v.name v.code)
      (Spec.Ffdh.sievedParameterCandidateContract abi 184) := by
  cases umaal with
  | false => exact candidate_verified v
  | true => exact VG.Proof.Ffdh.Arm.CallerRows.verified (candidate_verified v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
