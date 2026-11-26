module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP320r1.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP320r1.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhBrainpoolP320r1.AArch64

open VG.Proof.BrainpoolP320r1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeBrainpoolP320r1
    verified := Proof.Ecdh.AArch64.BrainpoolP320r1.exchange_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP320r1.AArch64
