module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Secp256k1.PPC64LE.Law

/-! # ECDH over secp256k1 (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhSecp256k1.PPC64LE

open VG.Proof.Secp256k1.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.Secp256k1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.secp256k1Exchange
    verified := .scrubbed (Proof.Ecdh.PPC64LE.Scrub.secp256k1Exchange_scrubbed hasLaw.law) }]

end VG.Artifacts.EcdhSecp256k1.PPC64LE
