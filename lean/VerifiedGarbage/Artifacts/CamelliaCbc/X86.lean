module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiScrub
public import VerifiedGarbage.Impl.Camellia.X86.AesNiFn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Camellia.X86.CbcLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit

/-! # Camellia-CBC on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNi.Fn.cbcEncryptChained
    verified := Proof.Camellia.X86.AesNi.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cbcEncryptChained
    verified := Proof.Camellia.X86.Scrub.cbcEncryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.cbcDecryptChained
    verified := Proof.Camellia.X86.AesNiWide.Scrub.cbcDecryptChained_scrubbed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.Camellia.X86.Fn.cbcDecryptChained
    verified := Proof.Camellia.X86.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.CamelliaCbc.X86
