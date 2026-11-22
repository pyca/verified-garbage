module

public import VerifiedGarbage.Proof.Seed.X86.Scrub
public import VerifiedGarbage.Impl.Seed.X86.Fn
public import VerifiedGarbage.Proof.Seed.X86.AesNiScrub
public import VerifiedGarbage.Impl.Seed.X86.AesNiFn
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Seed.X86.FbFinalLit
import VerifiedGarbage.Proof.Seed.X86.AesNiLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit

/-! # SEED-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.X86

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbEncrypt
    verified := Proof.Seed.X86.AesNi.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbEncryptApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cfbEncrypt
    verified := Proof.Seed.X86.Scrub.cfbEncrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNiWide.Fn.cfbDecrypt
    verified := Proof.Seed.X86.AesNiWide.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cfbDecrypt
    verified := Proof.Seed.X86.Scrub.cfbDecrypt_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbEncryptFinal
    verified := Proof.Seed.X86.AesNi.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cfbEncryptFinal
    verified := Proof.Seed.X86.Scrub.cfbEncryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNi.Fn.cfbDecryptFinal
    verified := Proof.Seed.X86.AesNi.Scrub.cfbDecryptFinal_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.cfbDecryptFinal
    verified := Proof.Seed.X86.Scrub.cfbDecryptFinal_scrubbed }]

end VG.Artifacts.SeedCfb.X86
