module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Mcdt
import VerifiedGarbage.Proof.Mcdt.X86_64
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Intel's MXCSR mitigation of MCDT on x86-64 -/

namespace VG.Artifacts.Mcdt.X86_64

public def artifacts : List (Artifact X86_64.target) := [
  Spec.Mcdt.enterApi.artifact X86_64.target {
    code := Impl.Mcdt.X86_64.enterCall
    verified := Proof.Mcdt.X86_64.enter_scrubbed
    spSafe := Proof.Mcdt.X86_64.enter_spSafe
    modeOk := Proof.Mcdt.X86_64.enter_mode }]

spec_apis artifacts

end VG.Artifacts.Mcdt.X86_64
