module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Contract
import VerifiedGarbage.Proof.Blowfish.X86.Scrub
import VerifiedGarbage.Impl.Blowfish.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Verified
import VerifiedGarbage.Impl.Blowfish.X86.Ssse3
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideVerified
import VerifiedGarbage.Impl.Blowfish.X86.Ssse3Wide
import VerifiedGarbage.Proof.Blowfish.X86.Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3Lit
import VerifiedGarbage.Proof.Blowfish.X86.Ssse3WideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish on x86 -/

namespace VG.Artifacts.Blowfish.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Fn.expandKey
    verified := Proof.Blowfish.X86.Ssse3.expandKey_scrubbed },
  Spec.Blowfish.expandKeyApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.expandKey
    verified := Proof.Blowfish.X86.Scrub.expandKey_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Wide.Fn.ecbEncrypt
    verified := Proof.Blowfish.X86.Ssse3.Wide.Ecb.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbEncryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbEncrypt
    verified := Proof.Blowfish.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    suffix := "_ssse3"
    code := Impl.Blowfish.X86.Ssse3.Wide.Fn.ecbDecrypt
    verified := Proof.Blowfish.X86.Ssse3.Wide.Ecb.ecbDecrypt_scrubbed },
  Spec.Blowfish.ecbDecryptApi.artifact X86.target {
    code := Impl.Blowfish.X86.Fn.ecbDecrypt
    verified := Proof.Blowfish.X86.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Blowfish.X86
