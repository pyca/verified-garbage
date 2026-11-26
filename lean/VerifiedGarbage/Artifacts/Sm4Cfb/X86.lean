module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Proof.Sm4.X86.Scrub
import VerifiedGarbage.Impl.Sm4.X86.Fn
import VerifiedGarbage.Proof.Sm4.X86.AesNiScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on x86 -/

namespace VG.Artifacts.Sm4Cfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm4.cfbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.cfbEncrypt
    verified := Proof.Sm4.X86.AesNi.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbEncryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbEncrypt
    verified := Proof.Sm4.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.cfbDecrypt
    verified := Proof.Sm4.X86.AesNiWide.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbDecryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbDecrypt
    verified := Proof.Sm4.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.cfbEncryptFinal
    verified := Proof.Sm4.X86.AesNi.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbEncryptFinal
    verified := Proof.Sm4.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.cfbDecryptFinal
    verified := Proof.Sm4.X86.AesNi.Scrub.cfbDecryptFinal_scrubbed },
  Spec.Sm4.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cfbDecryptFinal
    verified := Proof.Sm4.X86.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.X86
