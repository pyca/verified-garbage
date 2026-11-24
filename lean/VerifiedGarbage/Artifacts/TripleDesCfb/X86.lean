module

public import VerifiedGarbage.Proof.TripleDes.X86.Scrub
public import VerifiedGarbage.Impl.TripleDes.X86.Fn
public import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
public import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit

/-! # Triple DES-CFB64 on x86 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.X86

def artifacts : List (Artifact X86.target) := [
  Spec.TripleDes.cfbEncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cfbEncrypt
    verified := Proof.TripleDes.X86.Ssse3.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbEncryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbEncrypt
    verified := Proof.TripleDes.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.TripleDes.cfbDecryptApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbDecrypt
    verified := Proof.TripleDes.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.X86.Ssse3.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.TripleDes.X86.Ssse3.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.X86.Ssse3.cfbDecryptFinal_scrubbed },
  Spec.TripleDes.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.TripleDes.X86.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.TripleDesCfb.X86
