module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P256.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-256 (SP 800-56A) on PPC64LE -/

namespace VG.Artifacts.EcdhP256.PPC64LE

open VG.Proof.P256.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdh.P256.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.p256Exchange
    verified := Proof.Ecdh.PPC64LE.Scrub.p256Exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP256.PPC64LE
