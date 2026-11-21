module

public import VerifiedGarbage.Impl.Ecdh.P192.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.P192.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P192.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P192
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over P-192 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP192.AArch64

open VG.Proof.P192.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P192.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP192
    verified := Proof.Ecdh.AArch64.P192.exchange_scrubbed hasLaw.law hasLaw.inv }]

end VG.Artifacts.EcdhP192.AArch64
