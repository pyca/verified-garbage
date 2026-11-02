module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CT
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! # An FFDH parameter candidate on PPC64LE, verified for any round -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- `vg_ffdh_parameter_candidate` meets its contract, for any implementation
of the round. -/
theorem pc_verified (R : RoundImpl) :
    Verified target (VG.Impl.Ffdh.PPC64LE.ParameterCandidate.code R.name R.code)
      (Proof.Ffdh.parameterCandidateContract abi 176) :=
  Verified.of_correct (code_correct R) (code_ct R) pc_implies

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
