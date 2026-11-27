module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.Impl.Ecdh.P192.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P192.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P192.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-192 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P192.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP192
    verified := Proof.Ecdh.AArch64.P192.exchange_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcdhP192.AArch64
