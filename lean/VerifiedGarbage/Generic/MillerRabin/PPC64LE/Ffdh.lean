module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # FFDH parameter generation calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.PPC64LE.Ffdh

def artifacts (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Ffdh.parameterCandidateApi.artifact PPC64LE.target {
    suffix := v.suffix
    notes := ["The candidate's shape, congruence and trial division use the verified bignum \
        code shared with the prime search. Both primes use the shared `vg_miller_rabin_round` \
        with fixed four-bit windows, with 64 or 128 witnesses for each, every witness drawn from \
        `rand`. Every value is public: branches follow the tape, the shape and the witnesses' \
        results. The nonvolatile registers it uses are saved at the end of `scratch`; the round \
        it calls uses 176 bytes of stack."]
    code := Impl.Ffdh.PPC64LE.ParameterCandidate.code v.name v.code
    stack := 176
    verified := Proof.Ffdh.PPC64LE.ParameterCandidate.pc_verified v
    features := v.features },
  Spec.Ffdh.parameterSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    stack := 336
    notes := ["The whole candidate search runs in verified code: the attempt limit, the \
        octets each rejected candidate consumed, and the length of the next entropy \
        request. Each candidate calls `vg_ffdh_parameter_candidate` with the same round, in a \
        frame of 112 bytes holding its stack argument, within a frame saving the link register. \
        The random tape and the controller's four public words are public under the contract."]
    code := Proof.Ffdh.PPC64LE.Generation.searchCode v
    verified := Proof.Ffdh.PPC64LE.Generation.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.PPC64LE.Ffdh
