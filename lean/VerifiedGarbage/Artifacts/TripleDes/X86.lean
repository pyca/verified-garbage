module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit

/-! # Triple DES on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.X86

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.expandKey
    verified := Proof.TripleDes.X86.Scrub.expandKey_scrubbed },
  Spec.TripleDes.ecbEncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ecbEncrypt
    verified := Proof.TripleDes.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.TripleDes.ecbDecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.ecbDecrypt
    verified := Proof.TripleDes.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.TripleDes.X86
