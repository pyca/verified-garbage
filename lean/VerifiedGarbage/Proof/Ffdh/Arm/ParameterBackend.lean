module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Verified
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Stack
public import VerifiedGarbage.Spec.Ffdh.SievedContract

/-! A verified parameter candidate supplied to the native retry/refill controller. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure ParameterBackend where
  candidate : Prog isa
  candidate_verified : Verified target candidate (Spec.Ffdh.sievedParameterCandidateContract abi 184)
  candidateStack : FrameStack.armStack candidate ≤ 184
  suffix : String
  features : List String

def ParameterBackend.candidateName (b : ParameterBackend) : String :=
  Spec.Ffdh.sievedParameterCandidateApi.name ++ b.suffix

def parameterBackend (v : VG.Proof.MillerRabin.Arm.RoundImpl) : ParameterBackend := by
  exact {
    candidate := VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode (v.features.contains "umaal") v.name v.code
    candidate_verified := by exact ParameterCandidate.optimizedCandidate_verified _ v
    candidateStack := by exact ParameterCandidate.optimizedCandidate_stack _ v
    suffix := v.suffix
    features := v.features }

end VG.Proof.Ffdh.Arm
