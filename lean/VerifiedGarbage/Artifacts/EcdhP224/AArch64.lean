module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P224
import VerifiedGarbage.Impl.Ecdh.P224.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P224.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-224 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P224.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP224
    verified := Proof.Ecdh.AArch64.P224.exchange_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcdhP224.AArch64
