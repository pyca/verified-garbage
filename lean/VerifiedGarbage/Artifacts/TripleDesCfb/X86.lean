module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbEncrypt
    verified := Proof.TripleDes.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbDecrypt
    verified := Proof.TripleDes.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.TripleDesCfb.X86
