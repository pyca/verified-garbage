module

public import VerifiedGarbage.Proof.Camellia.X86.SseExpandKey
public import VerifiedGarbage.Impl.Camellia.X86.SseExpandKey
public import VerifiedGarbage.Proof.Camellia.X86.SseEcb
public import VerifiedGarbage.Impl.Camellia.X86.SseFn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiExpandKey
public import VerifiedGarbage.Impl.Camellia.X86.AesNiExpandKey
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideEcb
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideEcb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.SseKeyLit
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiKeyLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit

/-! # Camellia on x86 -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
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

end VG.Artifacts.Camellia.X86
