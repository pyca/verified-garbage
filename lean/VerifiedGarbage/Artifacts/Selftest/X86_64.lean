module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Selftest.Contract
import VerifiedGarbage.Proof.Selftest.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # The emitter's self-test on x86-64 -/

namespace VG.Artifacts.Selftest.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  { api := Spec.Selftest.addApi
    code := Proof.Selftest.X86_64.addScrubbed
    contract := Spec.Selftest.addContract X86_64.abi
    verified := ⟨Proof.Selftest.X86_64.addScrubbed_verified,
      Proof.Selftest.X86_64.addScrubbed_noResidue,
      Proof.Selftest.X86_64.addScrubbed_retAbi⟩ }]

spec_apis artifacts

end VG.Artifacts.Selftest.X86_64
