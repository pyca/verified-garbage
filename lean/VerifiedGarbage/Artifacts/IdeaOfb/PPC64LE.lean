module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Ofb
public import VerifiedGarbage.Spec.Idea.OfbFinal
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-OFB on PPC64LE -/

namespace VG.Artifacts.IdeaOfb.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Idea.ofbApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.ofb
    verified := Proof.Idea.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.ofbFinal
    verified := Proof.Idea.PPC64LE.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.IdeaOfb.PPC64LE
