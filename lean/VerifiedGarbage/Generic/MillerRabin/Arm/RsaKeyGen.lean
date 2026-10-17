module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA candidates on ARMv7 call each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.Arm.RsaKeyGen

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact := [
  Spec.RsaKeyGen.candidateApi.artifact Arm.target {
    suffix := v.suffix
    notes := ["Baseline ARMv7, on the working space of the RSA key routines, in 32-bit limbs: the \
        candidate's check against `p` under masks; trial division by Montgomery reduction of the \
        candidate's 16-bit halves modulo each small prime, with `−s⁻¹ mod 2^16` by Newton's \
        iteration; `gcd(c − 1, e)` by the binary extended Euclidean algorithm; then Montgomery \
        multiplication modulo the candidate, whose working space is the key arrays from 21 on, \
        and each witness, fixed under masks, in Montgomery form for a call of the shared \
        `vg_miller_rabin_round`, whose frame takes the 56 bytes below this function's. Branches \
        release only the checks and witness results allowed by the RSA candidate contract."]
    code := Impl.RsaKeyGen.Arm.Candidate.code v.name v.code
    stack := 112
    verified := Proof.RsaKeyGen.Arm.Cand.cand_verified v
    features := v.features }]

end VG.Generic.MillerRabin.Arm.RsaKeyGen
