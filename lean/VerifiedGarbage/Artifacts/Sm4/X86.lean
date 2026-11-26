module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Proof.Sm4.X86.Scrub
import VerifiedGarbage.Impl.Sm4.X86.Fn
import VerifiedGarbage.Proof.Sm4.X86.AesNiKey
import VerifiedGarbage.Impl.Sm4.X86.AesNiKey
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideEcb
import VerifiedGarbage.Impl.Sm4.X86.AesNiWideEcb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.Lit
import VerifiedGarbage.Proof.Sm4.X86.AesNiKeyLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on x86 -/

namespace VG.Artifacts.Sm4.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm4.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiKey.Fn.expandKey
    verified := Proof.Sm4.X86.AesNiKey.expandKey_scrubbed },
  Spec.Sm4.expandKeyApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.expandKey
    verified := Proof.Sm4.X86.Scrub.expandKey_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.ecbEncrypt
    verified := Proof.Sm4.X86.AesNiWide.Ecb.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ecbEncrypt
    verified := Proof.Sm4.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.ecbDecrypt
    verified := Proof.Sm4.X86.AesNiWide.Ecb.ecbDecrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ecbDecrypt
    verified := Proof.Sm4.X86.Scrub.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4.X86
