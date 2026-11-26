module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.PPC64LE.Verified
import VerifiedGarbage.Proof.X448.PPC64LE.Exchange
import VerifiedGarbage.Proof.X448.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on PPC64LE -/

namespace VG.Artifacts.X448.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.X448.exchangeApi.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.Fn.exchange
    verified := Proof.X448.PPC64LE.Scrub.exchange_scrubbed },
  Spec.X448.x448BaseApi.artifact PPC64LE.target {
    code := Impl.X448.PPC64LE.Fn.base
    verified := Proof.X448.PPC64LE.Scrub.base_scrubbed }]

spec_apis artifacts

end VG.Artifacts.X448.PPC64LE
