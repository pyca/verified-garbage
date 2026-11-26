module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Seed.Contract
import VerifiedGarbage.Proof.Seed.X86.ExpandKey
import VerifiedGarbage.Impl.Seed.X86.ExpandKey
import VerifiedGarbage.Proof.Seed.X86.SseEcb
import VerifiedGarbage.Impl.Seed.X86.SseFn
import VerifiedGarbage.Proof.Seed.X86.AesNiWideEcb
import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.ExpandKeyLit
import VerifiedGarbage.Proof.Seed.X86.SseLit
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SEED on x86 -/

namespace VG.Artifacts.Seed.X86

public def artifacts : List (Artifact X86.target) := [
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

spec_apis artifacts

end VG.Artifacts.Seed.X86
