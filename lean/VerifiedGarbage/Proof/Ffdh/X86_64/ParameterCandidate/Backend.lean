module

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT

/-! # FFDH parameter generation on x86-64: verify every shared arithmetic backend -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64

theorem candidateCode_verified (v : RoundImpl) : Verified target (candidateCode v)
    (Proof.Ffdh.parameterCandidateContract abi 128) := by
  exact Verified.of_correct
    (pc_correct v.mont (R2Impl.words v.mont) (Kernel.called v)
      (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_mx v))
    (pc_constantTime v.mont (R2Impl.words v.mont) (Kernel.called v)) pc_implies

end VG.Proof.Ffdh.X86_64.ParameterCandidate
