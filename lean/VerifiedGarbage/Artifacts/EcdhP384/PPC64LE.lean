module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.P384.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over P-384 (SP 800-56A) on PPC64LE -/

namespace VG.Artifacts.EcdhP384.PPC64LE

open VG.Proof.P384.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdh.P384.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.p384Exchange
    verified := Proof.Ecdh.PPC64LE.Scrub.p384Exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhP384.PPC64LE
