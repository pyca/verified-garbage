module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Proof.Ct.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on PPC64LE -/

namespace VG.Artifacts.Ct.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Ct.eqApi.artifact PPC64LE.target {
    code := Impl.Ct.PPC64LE.Fn.eq
    verified := Proof.Ct.PPC64LE.Scrub.eq_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Ct.PPC64LE
