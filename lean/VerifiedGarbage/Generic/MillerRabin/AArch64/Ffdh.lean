module

import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.CTCode
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Verified
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

/-! # FFDH parameter generation calls each shared Miller–Rabin implementation -/

@[expose] public section

namespace VG.Generic.MillerRabin.AArch64.Ffdh

def artifacts (v : Proof.MillerRabin.AArch64.RoundImpl) : List Artifact := [
  Spec.Ffdh.parameterCandidateApi.artifact AArch64.target {
    suffix := v.suffix
    notes := ["The candidate's shape, congruence and trial division use RSA's verified \
        bignum code. Both primes use the shared `vg_miller_rabin_round` with fixed four-bit \
        windows, with 64 or 128 witnesses for each, every witness drawn from `rand`. \
        Every value is public: branches follow the tape, the shape and the witnesses' results."]
    code := Impl.Ffdh.AArch64.ParameterCandidate.code v.mont.mm v.kernel.run
    verified := Proof.Ffdh.AArch64.ParameterCandidate.pc_verified v.mont v.kernel
    features := v.features },
  Spec.Ffdh.parameterSearchApi.artifact AArch64.target {
    suffix := v.suffix
    stack := 32
    notes := ["The whole candidate search runs in verified code: the attempt limit, the \
        octets each rejected candidate consumed, and the length of the next entropy \
        request. Each candidate calls `vg_ffdh_parameter_candidate` with the same round, in a \
        frame of 16 bytes holding its stack argument, within a frame saving `x30`. The random \
        tape and the controller's four public words are public under the contract."]
    code := Proof.Ffdh.AArch64.Generation.searchCode v
    verified := Proof.Ffdh.AArch64.Generation.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.Ffdh
