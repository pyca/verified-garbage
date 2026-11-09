module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit

/-! # IDEA-CFB64 artifacts on baseline PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncrypt
    stack := 96
    verified := Proof.Idea.PPC64LE.cfbEnc_framed Proof.Idea.PPC64LE.Modes.cfbEncrypt_verified },
  Spec.Idea.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecrypt
    stack := 96
    verified := Proof.Idea.PPC64LE.cfbDec_framed Proof.Idea.PPC64LE.Modes.cfbDecrypt_verified },
  Spec.Idea.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbEncryptFinal
    stack := 96
    verified := Proof.Idea.PPC64LE.FbFinal.cfbEncryptFinal_framed },
  Spec.Idea.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r7 8 Impl.Idea.PPC64LE.cfbDecryptFinal
    stack := 96
    verified := Proof.Idea.PPC64LE.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.IdeaCfb.PPC64LE
