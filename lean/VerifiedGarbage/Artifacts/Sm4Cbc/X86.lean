module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.X86.Scrub
import VerifiedGarbage.Impl.Sm4.X86.Fn
import VerifiedGarbage.Proof.Sm4.X86.AesNiScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiFn
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.CbcLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on x86 -/

namespace VG.Artifacts.Sm4Cbc.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNi.Fn.cbcEncryptChained
    verified := Proof.Sm4.X86.AesNi.Scrub.cbcEncryptChained_scrubbed },
  Spec.Sm4.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cbcEncryptChained
    verified := Proof.Sm4.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.cbcDecryptChained
    verified := Proof.Sm4.X86.AesNiWide.Scrub.cbcDecryptChained_scrubbed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.cbcDecryptChained
    verified := Proof.Sm4.X86.Scrub.cbcDecryptChained_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.X86
