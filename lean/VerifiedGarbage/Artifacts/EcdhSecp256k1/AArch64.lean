module

public import VerifiedGarbage.Impl.Ecdh.Secp256k1.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Secp256k1.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over secp256k1 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhSecp256k1.AArch64

open VG.Proof.Secp256k1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeSecp256k1
    verified := .scrubbed (Proof.Ecdh.AArch64.Secp256k1.exchange_scrubbed hasLaw.law hasLaw.inv) }]

end VG.Artifacts.EcdhSecp256k1.AArch64
