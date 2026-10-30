module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit

/-! # IDEA-OFB artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.ofbApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.ofb
    stack := 96
    verified := Proof.Idea.PPC64LE.ofb_framed Proof.Idea.PPC64LE.Modes.ofb_verified }]

end VG.Artifacts.IdeaOfb.PPC64LE
