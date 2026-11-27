module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Cfb
public import VerifiedGarbage.Spec.Seed.CfbFinal
import VerifiedGarbage.Proof.Seed.X86.SseScrub
import VerifiedGarbage.Impl.Seed.X86.SseFn
import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
import VerifiedGarbage.Impl.Seed.X86.AesNiFn
import VerifiedGarbage.Proof.Seed.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED-CFB128 on x86 -/

namespace VG.Artifacts.SeedCfb.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbEncrypt
    verified := Proof.Seed.X86.AesNi.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cfbEncrypt
    verified := Proof.Seed.X86.Sse.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNiWide.Fn.cfbDecrypt
    verified := Proof.Seed.X86.AesNiWide.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cfbDecrypt
    verified := Proof.Seed.X86.Sse.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbEncryptFinal
    verified := Proof.Seed.X86.AesNi.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cfbEncryptFinal
    verified := Proof.Seed.X86.Sse.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbDecryptFinal
    verified := Proof.Seed.X86.AesNi.Scrub.cfbDecryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.cfbDecryptFinal
    verified := Proof.Seed.X86.Sse.Scrub.cfbDecryptFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.SeedCfb.X86
