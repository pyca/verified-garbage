module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over secp256k1 (SP 800-56A) on PPC64LE -/

namespace VG.Artifacts.EcdhSecp256k1.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.secp256k1Exchange
    verified := Proof.Ecdh.PPC64LE.Scrub.secp256k1Exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhSecp256k1.PPC64LE
