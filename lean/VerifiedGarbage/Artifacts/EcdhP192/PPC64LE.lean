module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.P192.PPC64LE.Law

/-! # ECDH over P-192 (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.EcdhP192.PPC64LE

open VG.Proof.P192.PPC64LE (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.p192Exchange
    verified := .scrubbed (Proof.Ecdh.PPC64LE.Scrub.p192Exchange_scrubbed hasLaw.law) }]

end VG.Artifacts.EcdhP192.PPC64LE
