module

public import VerifiedGarbage.Proof.Idea.X86.Scrub
public import VerifiedGarbage.Impl.Idea.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Idea.X86.ModesLit
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit

/-! # IDEA-OFB on x86 -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.X86

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ofb
    verified := .scrubbed Proof.Idea.X86.Scrub.ofb_scrubbed },
  Spec.Idea.ofbFinalApi.artifact X86.target {
    code := Impl.Idea.X86.Fn.ofbFinal
    verified := .scrubbed Proof.Idea.X86.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.IdeaOfb.X86
