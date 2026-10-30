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
    code := Impl.Ffdh.AArch64.ParameterCandidate.code v.mont.mm v.kernel.run
    verified := Proof.Ffdh.AArch64.ParameterCandidate.pc_verified v.mont v.kernel
    features := v.features },
  Spec.Ffdh.parameterSearchApi.artifact AArch64.target {
    suffix := v.suffix
    stack := 32
    code := Proof.Ffdh.AArch64.Generation.searchCode v
    verified := Proof.Ffdh.AArch64.Generation.search_verified v
    features := v.features }]

end VG.Generic.MillerRabin.AArch64.Ffdh
