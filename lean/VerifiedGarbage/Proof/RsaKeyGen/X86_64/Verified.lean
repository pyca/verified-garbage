import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTCode
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Implies

/-!
# A candidate for an RSA prime on x86-64: verified against the shared contract

With correctness (`code_correct`), constant time (`code_constantTime`) and
the shared contract's implication (`cand_implies`), `code` is verified for
any Montgomery multiplication (`candidate_verified`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- `vg_rsa_keygen_candidate` with Montgomery multiplication `M`, given that
its code never loads MXCSR (which the registration file evaluates). -/
theorem candidate_verified (M : Mont)
    (hmx : (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (VG.Impl.RsaKeyGen.X86_64.Candidate.code M.mm) (Spec.RsaKeyGen.candidateContract abi) :=
  Verified.of_correct (code_correct M hmx) (code_constantTime M) cand_implies

end VG.Proof.RsaKeyGen.X86_64
