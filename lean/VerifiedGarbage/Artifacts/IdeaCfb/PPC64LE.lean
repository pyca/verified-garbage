module

public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Idea.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Idea.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.Proof.Idea.PPC64LE.ModesLit
import VerifiedGarbage.Proof.Idea.PPC64LE.FbFinalLit

/-! # IDEA-CFB64 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Idea.cfbEncryptApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbEncrypt
    verified := Proof.Idea.PPC64LE.Scrub.cfbEncrypt_scrubbed },
  Spec.Idea.cfbDecryptApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbDecrypt
    verified := Proof.Idea.PPC64LE.Scrub.cfbDecrypt_scrubbed },
  Spec.Idea.cfbEncryptFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbEncryptFinal
    verified := Proof.Idea.PPC64LE.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Idea.cfbDecryptFinalApi.artifact PPC64LE.target {
    code := Impl.Idea.PPC64LE.Fn.cfbDecryptFinal
    verified := Proof.Idea.PPC64LE.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.IdeaCfb.PPC64LE
