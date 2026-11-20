module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.AArch64
public import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.BrainpoolP320r1.AArch64.Law
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.EcdhBrainpoolP320r1.AArch64

open VG.Proof.BrainpoolP320r1.AArch64 (hasLaw)

def artifacts : List Artifact := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeBrainpoolP320r1
    verified := .scrubbed (Proof.Ecdh.AArch64.BrainpoolP320r1.exchange_scrubbed hasLaw.law hasLaw.inv) }]

end VG.Artifacts.EcdhBrainpoolP320r1.AArch64
