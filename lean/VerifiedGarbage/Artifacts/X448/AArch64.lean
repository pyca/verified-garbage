module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Impl.X448.AArch64.Fn
import VerifiedGarbage.Proof.X448.AArch64.Fast.Verified
import VerifiedGarbage.Proof.X448.AArch64.Base.Verified
import VerifiedGarbage.Proof.X448.AArch64.Exchange
import VerifiedGarbage.Proof.X448.AArch64.ExchangeResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.X448.AArch64.BaseScrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # X448 (RFC 7748) on AArch64 -/

namespace VG.Artifacts.X448.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.X448.exchangeApi.artifact AArch64.target {
    code := Impl.X448.AArch64.Fn.exchange
    verified := Proof.X448.AArch64.ExchangeResidue.exchangeCode_scrubbed },
  Spec.X448.x448BaseApi.artifact AArch64.target {
    code := Impl.X448.AArch64.Base.Fn.x448Base
    verified := Proof.X448.AArch64.BaseScrub.x448Base }]

spec_apis artifacts

end VG.Artifacts.X448.AArch64
