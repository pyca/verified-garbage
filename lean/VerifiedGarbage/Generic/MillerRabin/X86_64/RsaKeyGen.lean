module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedVerified

/-! # Emit RSA candidates for every shared Miller–Rabin backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact X86_64.target {
    suffix := v.suffix
    notes := ["The candidate checks retain RSA's witness selection and retry policy. Each \
        prepared witness calls the shared `vg_miller_rabin_round`, using fixed four-bit windows \
        and the selected verified Montgomery backend. Branches release only the checks and \
        witness results allowed by the RSA candidate contract."]
    code := Proof.RsaKeyGen.X86_64.sharedCandidateCode v
    stack := 128
    verified := Proof.RsaKeyGen.X86_64.sharedCandidate_verified v
    spSafe := Proof.RsaKeyGen.X86_64.sharedCandidate_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.RsaKeyGen
