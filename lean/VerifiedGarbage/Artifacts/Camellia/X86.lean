module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideEcb
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideEcb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.Lit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit

/-! # Camellia on x86 -/

@[expose] public section

namespace VG.Artifacts.Camellia.X86

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.expandKey
    verified := Proof.Camellia.X86.Scrub.expandKey_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ecbEncrypt
    verified := Proof.Camellia.X86.AesNiWide.Ecb.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbEncryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.ecbEncrypt
    verified := Proof.Camellia.X86.Scrub.ecbEncrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ecbDecrypt
    verified := Proof.Camellia.X86.AesNiWide.Ecb.ecbDecrypt_scrubbed },
  Spec.Camellia.ecbDecryptApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.ecbDecrypt
    verified := Proof.Camellia.X86.Scrub.ecbDecrypt_scrubbed }]

end VG.Artifacts.Camellia.X86
