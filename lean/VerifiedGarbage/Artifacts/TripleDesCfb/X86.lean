module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Proof.TripleDes.X86.Scrub
import VerifiedGarbage.Impl.TripleDes.X86.Fn
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Verified
import VerifiedGarbage.Impl.TripleDes.X86.Ssse3
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.Ssse3Lit
import VerifiedGarbage.Proof.TripleDes.X86.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86.FbLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on x86 -/

namespace VG.Artifacts.TripleDesCfb.X86

public def artifacts : List (Artifact X86.target) := [
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

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.X86
