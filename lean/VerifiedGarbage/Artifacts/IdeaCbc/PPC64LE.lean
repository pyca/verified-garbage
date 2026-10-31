module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit

/-! # IDEA-CBC artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcEncryptChained
    stack := 96
    verified := Proof.Idea.PPC64LE.cbcEnc_framed Proof.Idea.PPC64LE.Modes.cbcEncryptChained_verified },
  Spec.Idea.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cbcDecryptChained
    stack := 96
    verified := Proof.Idea.PPC64LE.cbcDec_framed Proof.Idea.PPC64LE.Modes.cbcDecryptChained_verified }]

end VG.Artifacts.IdeaCbc.PPC64LE
