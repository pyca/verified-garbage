module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.P256.EcdhJac.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-256 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P256.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP256
    verified := Proof.P256.EcdhJac.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime hasLaw.invToMP }]

spec_apis artifacts

end VG.Artifacts.EcdhP256.AArch64
