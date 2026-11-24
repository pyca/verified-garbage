module

public import VerifiedGarbage.Proof.Cast5.X86.Scrub
public import VerifiedGarbage.Impl.Cast5.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideVerified
public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Wide
public import VerifiedGarbage.Proof.Cast5.X86.Ssse3KeyVerified
public import VerifiedGarbage.Impl.Cast5.X86.Ssse3Key
import VerifiedGarbage.Proof.Cast5.X86.Ssse3Lit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Cast5.X86.Ssse3KeyLit

/-! # CAST5 (RFC 2144) on x86 -/

@[expose] public section

namespace VG.Artifacts.Cast5.X86

def artifacts : List (Artifact X86.target) := [
  Spec.Cast5.expandKeyApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Key.Fn.expandKey
    verified := Proof.Cast5.X86.Ssse3.Key.expandKey_scrubbed },
  Spec.Cast5.expandKeyApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.expandKey
    verified := Proof.Cast5.X86.Scrub.expandKey_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Wide.Fn.ecbEncrypt
    verified := Proof.Cast5.X86.Ssse3.Wide.Ecb.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbEncryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ecbEncrypt
    verified := Proof.Cast5.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Cast5.X86.Ssse3.Wide.Fn.ecbDecrypt
    verified := Proof.Cast5.X86.Ssse3.Wide.Ecb.ecbDecrypt_scrubbed },
  Spec.Cast5.ecbDecryptApi.artifact X86.target {
    code := Impl.Cast5.X86.Fn.ecbDecrypt
    verified := Proof.Cast5.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Cast5.X86
