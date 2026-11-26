module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Proof.Ct.X86.Scrub
import VerifiedGarbage.Impl.Ct.X86
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on x86 -/

namespace VG.Artifacts.Ct.X86
open VG.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.X86.Fn.eq
    verified := Proof.Ct.X86.Scrub.eq_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ct.X86
