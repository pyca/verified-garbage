module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Impl.Ecdh.P384.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP384
    verified := Proof.Ecdh.AArch64.P384.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.AArch64
