module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Impl.Ecdh.P521.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P521.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-521 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP521.AArch64

open VG.Proof.P521.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P521.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP521
    verified := Proof.Ecdh.AArch64.P521.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime }]

spec_apis artifacts

end VG.Artifacts.EcdhP521.AArch64
