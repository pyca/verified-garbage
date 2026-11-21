module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit

/-! # IDEA-OFB on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.ofb
    verified := Proof.Idea.PPC64LE.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.ofbFinal
    verified := Proof.Idea.PPC64LE.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.IdeaOfb.PPC64LE
