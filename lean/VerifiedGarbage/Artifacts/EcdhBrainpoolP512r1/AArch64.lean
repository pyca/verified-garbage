module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP512r1
import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.AArch64
import VerifiedGarbage.Proof.Ecdh.AArch64.BrainpoolP512r1.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP512r1.AArch64.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP512r1 (SP 800-56A) on AArch64 -/

namespace VG.Artifacts.EcdhBrainpoolP512r1.AArch64

open VG.Proof.BrainpoolP512r1.AArch64 (hasLaw)

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Ecdh.BrainpoolP512r1.exchangeApi.artifact AArch64.target {
    code := Impl.Ecdh.AArch64.Fn.exchangeBrainpoolP512r1
    verified := Proof.Ecdh.AArch64.BrainpoolP512r1.exchange_scrubbed hasLaw.law hasLaw.inv }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP512r1.AArch64
