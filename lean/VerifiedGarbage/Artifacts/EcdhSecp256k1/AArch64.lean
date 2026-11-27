module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Secp256k1.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over secp256k1 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeSecp256k1
    verified := Proof.Ecdh.AArch64.Secp256k1.exchange_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcdhSecp256k1.AArch64
