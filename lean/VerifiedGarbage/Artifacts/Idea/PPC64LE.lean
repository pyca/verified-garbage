module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Contract
import VerifiedGarbage.Proof.Idea.PPC64LE.Invert
import VerifiedGarbage.Proof.Idea.PPC64LE.Key
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
import VerifiedGarbage.Proof.Idea.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA on PPC64LE -/

namespace VG.Artifacts.Idea.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Idea.expandKeyApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.expandKey
    verified := Proof.Idea.PPC64LE.Scrub.expandKey_scrubbed },
  Spec.Idea.invertKeyApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.invertKey
    verified := Proof.Idea.PPC64LE.Scrub.invertKey_scrubbed },
  Spec.Idea.ecbApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.ecb
    verified := Proof.Idea.PPC64LE.Scrub.ecb_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Idea.PPC64LE
