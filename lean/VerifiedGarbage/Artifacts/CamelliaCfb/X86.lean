module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Proof.Camellia.X86.SseScrub
import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on x86 -/

namespace VG.Artifacts.CamelliaCfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.cfbEncrypt
    verified := Proof.Camellia.X86.AesNi.Scrub.cfbEncrypt_scrubbed },
  Spec.Camellia.cfbEncryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cfbEncrypt
    verified := Proof.Camellia.X86.Sse.Scrub.cfbEncrypt_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.cfbDecrypt
    verified := Proof.Camellia.X86.AesNiWide.Scrub.cfbDecrypt_scrubbed },
  Spec.Camellia.cfbDecryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cfbDecrypt
    verified := Proof.Camellia.X86.Sse.Scrub.cfbDecrypt_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.cfbEncryptFinal
    verified := Proof.Camellia.X86.AesNi.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Camellia.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cfbEncryptFinal
    verified := Proof.Camellia.X86.Sse.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.cfbDecryptFinal
    verified := Proof.Camellia.X86.AesNi.Scrub.cfbDecryptFinal_scrubbed },
  Spec.Camellia.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.cfbDecryptFinal
    verified := Proof.Camellia.X86.Sse.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.X86
