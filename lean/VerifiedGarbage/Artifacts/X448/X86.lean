module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.X86.Verified
import VerifiedGarbage.Proof.X448.X86.Base
import VerifiedGarbage.Proof.Ed448.SignedCombFacts
import VerifiedGarbage.Proof.X448.X86.Lit
import VerifiedGarbage.Proof.X448.X86.Exchange
import VerifiedGarbage.Proof.X448.X86.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Impl.X448.X86.Base
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on x86 -/

namespace VG.Artifacts.X448.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.X448.exchangeApi.artifact X86.target {
    code := Impl.X448.X86.Fn.exchange
    verified := Proof.X448.X86.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact X86.target {
    code := Impl.X448.X86.Fn.base
    verified := Proof.X448.X86.Scrub.base_scrubbed }]

spec_apis artifacts

end VG.Artifacts.X448.X86
