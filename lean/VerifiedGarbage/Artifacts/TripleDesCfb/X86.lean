module

public import VerifiedGarbage.Proof.TripleDes.X86.FbVerified
public import VerifiedGarbage.Proof.TripleDes.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncrypt
    verified := .unscrubbed Proof.TripleDes.X86.Fb.cfbEncrypt_framed },
  Spec.TripleDes.cfbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1232 4 302 Impl.TripleDes.X86.cfbDecrypt
    verified := .unscrubbed Proof.TripleDes.X86.Fb.cfbDecrypt_framed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbEncryptFinal
    verified := .unscrubbed Proof.TripleDes.X86.FbFinal.cfbEncryptFinal_framed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 968 4 236 Impl.TripleDes.X86.cfbDecryptFinal
    verified := .unscrubbed Proof.TripleDes.X86.FbFinal.cfbDecryptFinal_framed }]

end VG.Artifacts.TripleDesCfb.X86
