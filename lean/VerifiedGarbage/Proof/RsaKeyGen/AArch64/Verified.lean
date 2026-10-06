import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTTail
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Implies
import VerifiedGarbage.Proof.Framework.Contract

/-!
# A candidate for an RSA prime on AArch64: verified against the shared contract

With correctness (`code_correct`), constant time (`code_constantTime`, from
`kMain_ct` and `kTail_ct`) and the shared contract's implication
(`cand_implies`), `code` is verified for any Montgomery multiplication
(`candidate_verified`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Proof.Bignum.AArch64

/-- `vg_rsa_keygen_candidate` with Montgomery multiplication `M`. -/
theorem candidate_verified (M : Mont) :
    Verified target (VG.Impl.RsaKeyGen.AArch64.Candidate.code M.mm) (Spec.RsaKeyGen.candidateContract abi) :=
  Verified.of_correct (code_correct M) (code_constantTime M (kMain_ct M (kTail_ct M))) cand_implies

end VG.Proof.RsaKeyGen.AArch64
