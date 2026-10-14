module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedVerified

/-! # RSA candidates call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.AArch64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  { Spec.RsaKeyGen.candidateApi with
    name := Spec.RsaKeyGen.candidateApi.name ++ v.suffix
    target := AArch64.target
    doc := Spec.RsaKeyGen.candidateApi.doc
      (notes := ["The candidate checks and RSA witness policy use the verified Montgomery \
        arithmetic. Each prepared witness calls the shared `vg_miller_rabin_round`, using \
        fixed four-bit windows. Branches release only the checks and witness results allowed \
        by the RSA candidate contract."])
    code := Impl.RsaKeyGen.AArch64.Candidate.codeWith v.mont.mm v.kernel.run
    contract := Spec.RsaKeyGen.candidateContract AArch64.abi
    verified := by exact Proof.RsaKeyGen.AArch64.sharedCandidate_verified v.mont v.kernel
    spSafe := Code.all_of_forall (fun _ => rfl) _
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.RsaKeyGen
