module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedSafety
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedImplies

/-! # Verify the RSA candidate against the existing shared ABI contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem sharedCandidate_verified (v : RoundImpl) : Verified target (sharedCandidateCode v)
    (Spec.RsaKeyGen.candidateContract abi 128) := by
  have hmc : MmCalls v.mont v.mm := ⟨v.mmOk, v.mmInline⟩
  exact Verified.of_correct
    (sharedCode_correct v.mont hmc (Kernel.called v) (sharedCandidate_mx v))
    (sharedCode_constantTime v.mont hmc (Kernel.called v)) sharedCand_implies

end VG.Proof.RsaKeyGen.X86_64
