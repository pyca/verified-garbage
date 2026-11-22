module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Sm4.X86.AesNiScrub
public import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Sm4.X86.FbLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit

/-! # SM4-CFB128 on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.X86

def artifacts : List Artifact := [
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

end VG.Artifacts.Sm4Cfb.X86
