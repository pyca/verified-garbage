module

public import VerifiedGarbage.Impl.Ecdh.P224.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.P224.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.P224.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.P224
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over P-224 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhP224.AArch64

open VG.Proof.P224.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.P224.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeP224
    verified := .scrubbed (Proof.Ecdh.AArch64.P224.exchange_scrubbed hasLaw.law hasLaw.inv) }]

end VG.Artifacts.EcdhP224.AArch64
