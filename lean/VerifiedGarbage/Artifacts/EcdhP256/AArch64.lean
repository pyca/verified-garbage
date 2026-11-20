module

public import VerifiedGarbage.Impl.P256.EcdhJac
public import VerifiedGarbage.Proof.P256.EcdhJac.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P256.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P256
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over P-256 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP256.AArch64

open VG.Proof.P256.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P256.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP256
    verified := .scrubbed (Proof.P256.EcdhJac.exchange_scrubbed hasLaw.law hasLaw.inv hasLaw.prime hasLaw.invToMP) }]

end VG.Artifacts.EcdhP256.AArch64
