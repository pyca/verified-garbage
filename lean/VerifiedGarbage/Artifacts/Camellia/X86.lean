module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Camellia.X86.SseExpandKey
import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
import VerifiedGarbage.Proof.Camellia.X86.SseEcb
import VerifiedGarbage.Impl.Camellia.X86.SseFn
import VerifiedGarbage.Proof.Camellia.X86.AesNiExpandKey
import VerifiedGarbage.Impl.Camellia.X86.AesNiExpandKey
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideEcb
import VerifiedGarbage.Impl.Camellia.X86.AesNiWideEcb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86.SseKeyLit
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiKeyLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on x86 -/

namespace VG.Artifacts.Camellia.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.expandKeyApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiKey.Fn.expandKey
    verified := Proof.Camellia.X86.AesNiKey.expandKey_scrubbed },
  Spec.Camellia.expandKeyApi.artifact X86.target {
    code := Impl.Camellia.X86.SseKey.Fn.expandKey
    verified := Proof.Camellia.X86.SseKey.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ecbEncrypt
    verified := Proof.Camellia.X86.AesNiWide.Ecb.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ecbEncrypt
    verified := Proof.Camellia.X86.Sse.Ecb.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ecbDecrypt
    verified := Proof.Camellia.X86.AesNiWide.Ecb.ecbDecrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ecbDecrypt
    verified := Proof.Camellia.X86.Sse.Ecb.ecbDecrypt_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Camellia.X86
