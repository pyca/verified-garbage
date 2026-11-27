module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.BrainpoolP320r1.PPC64LE.Law
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # ECDH over brainpoolP320r1 (SP 800-56A) on PPC64LE -/

namespace VG.Artifacts.EcdhBrainpoolP320r1.PPC64LE

open VG.Proof.BrainpoolP320r1.PPC64LE (hasLaw)

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ecdh.BrainpoolP320r1.exchangeApi.artifact PPC64LE.target {
    code := Impl.Ecdh.PPC64LE.Fn.brainpoolp320r1Exchange
    verified := Proof.Ecdh.PPC64LE.Scrub.brainpoolp320r1Exchange_scrubbed hasLaw.law }]

spec_apis artifacts

end VG.Artifacts.EcdhBrainpoolP320r1.PPC64LE
