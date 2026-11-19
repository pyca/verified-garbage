module

public import VerifiedGarbage.Impl.Ecdh.P384.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.P384.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P384.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P384
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over P-384 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP384.AArch64

open VG.Proof.P384.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P384.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP384
    verified := .scrubbed (Proof.Ecdh.AArch64.P384.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime) }]

end VG.Artifacts.EcdhP384.AArch64
