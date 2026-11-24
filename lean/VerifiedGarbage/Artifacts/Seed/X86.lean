module

public import VerifiedGarbage.Proof.Seed.X86.ExpandKey
public import VerifiedGarbage.Impl.Seed.X86.ExpandKey
public import VerifiedGarbage.Proof.Seed.X86.SseEcb
public import VerifiedGarbage.Impl.Seed.X86.SseFn
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideEcb
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.ExpandKeyLit
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit

/-! # SEED on x86 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86.target {
    code := Impl.Seed.X86.Fn.expandKey
    verified := Proof.Seed.X86.expandKey_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNiWide.Fn.ecbEncrypt
    verified := Proof.Seed.X86.AesNiWide.Ecb.ecbEncrypt_scrubbed },
  Spec.Seed.ecbEncryptApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.ecbEncrypt
    verified := Proof.Seed.X86.Sse.Ecb.ecbEncrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Seed.X86.AesNiWide.Fn.ecbDecrypt
    verified := Proof.Seed.X86.AesNiWide.Ecb.ecbDecrypt_scrubbed },
  Spec.Seed.ecbDecryptApi.artifact X86.target {
    code := Impl.Seed.X86.Sse.Fn.ecbDecrypt
    verified := Proof.Seed.X86.Sse.Ecb.ecbDecrypt_scrubbed }]

end VG.Artifacts.Seed.X86
