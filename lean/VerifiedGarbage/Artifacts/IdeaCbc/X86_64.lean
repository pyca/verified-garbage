module

public import VerifiedGarbage.Proof.Idea.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit

/-! # IDEA-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.IdeaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Idea.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcEncryptChained
    stack := 184
    verified := Proof.Idea.X86_64.cbcEncryptChained_framed },
  Spec.Idea.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 Impl.Idea.X86_64.cbcDecryptChained
    stack := 184
    verified := Proof.Idea.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.IdeaCbc.X86_64
