module

public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.Fn
public import VerifiedGarbage.Proof.Camellia.X86.SseScrub
public import VerifiedGarbage.Impl.Camellia.X86.SseFn
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Camellia.X86.SseLit
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
public import VerifiedGarbage.Proof.Variants.CamelliaCtr.X86

/-! # Camellia-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.X86

/-- `vg_camellia_ctr_final`, with each implementation of `vg_camellia_ctr`'s code. -/
def finals : List (Artifact X86.target) :=
  VG.Proof.Variants.CamelliaCtr.X86.variants.map fun (c : Proof.Camellia.X86.CtrFinal.CtrImpl) =>
    Spec.Camellia.ctrFinalApi.artifact X86.target {
      suffix := c.suffix
      code := Impl.Camellia.X86.Fn.ctrFinal c.name c.code c.words
      verified := Proof.Camellia.X86.Scrub.ctrFinal_scrubbed c
      spSafe := Proof.Camellia.X86.Scrub.ctrFinal_spSafeF c }

def artifacts : List (Artifact X86.target) := [
  Spec.Camellia.ctrApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Camellia.X86.AesNiWide.Fn.ctr
    verified := Proof.Camellia.X86.AesNiWide.Scrub.ctr_scrubbed },
  Spec.Camellia.ctrApi.artifact X86.target {
    code := Impl.Camellia.X86.Sse.Fn.ctr
    verified := Proof.Camellia.X86.Sse.Scrub.ctr_scrubbed }] ++ finals

end VG.Artifacts.CamelliaCtr.X86
