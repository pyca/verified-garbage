module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.X86.Scrub
import VerifiedGarbage.Impl.Cast5.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Verified
import VerifiedGarbage.Impl.Cast5.X86.Ssse3
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideVerified
import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
import VerifiedGarbage.Proof.Cast5.X86.ModesLit
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on x86 -/

namespace VG.Artifacts.Cast5Cfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbEncrypt
    verified := Proof.Cast5.X86.Ssse3.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbEncryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncrypt
    verified := Proof.Cast5.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Wide.Fn.cfbDecrypt
    verified := Proof.Cast5.X86.Ssse3.Wide.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbDecryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecrypt
    verified := Proof.Cast5.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbEncryptFinal
    verified := Proof.Cast5.X86.Ssse3.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbEncryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Fn.cfbDecryptFinal
    verified := Proof.Cast5.X86.Ssse3.cfbDecryptFinal_scrubbed },
  Spec.Cast5.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.cfbDecryptFinal
    verified := Proof.Cast5.X86.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.X86
