module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedVerified

/-! # RSA candidates call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.AArch64.RsaKeyGen

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["The candidate checks and RSA witness policy use the verified Montgomery \
        arithmetic. Each prepared witness calls the shared `vg_miller_rabin_round`, using \
        fixed four-bit windows. Branches release only the checks and witness results allowed \
        by the RSA candidate contract."]
    code := Impl.RsaKeyGen.AArch64.Candidate.codeWith v.mont.mm v.kernel.run
    verified := Proof.RsaKeyGen.AArch64.sharedCandidate_verified v.mont v.kernel
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.RsaKeyGen
