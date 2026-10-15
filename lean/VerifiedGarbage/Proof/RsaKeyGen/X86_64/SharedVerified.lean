module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedSafety
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedImplies
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Verify the RSA candidate against the existing shared ABI contract -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem sharedCandidate_verified (v : RoundImpl) : Verified target (sharedCandidateCode v)
    (Spec.RsaKeyGen.candidateContract abi 128) := by
  exact Verified.of_correct
    (sharedCode_correct v.mont (Kernel.called v) (sharedCandidate_mx v))
    (sharedCode_constantTime v.mont (Kernel.called v)) sharedCand_implies

end VG.Proof.RsaKeyGen.X86_64
