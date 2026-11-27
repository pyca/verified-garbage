module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.X86.Scrub
import VerifiedGarbage.Impl.Sm4.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideScrub
import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
import VerifiedGarbage.Proof.Sm4.X86.CtrLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
import VerifiedGarbage.Proof.Variants.Sm4Ctr.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on x86 -/

namespace VG.Artifacts.Sm4Ctr.X86

/-- `vg_sm4_ctr_final`, with each implementation of `vg_sm4_ctr`'s code. -/
def finals : List (Artifact X86.target) :=
  VG.Proof.Variants.Sm4Ctr.X86.variants.map fun (c : Proof.Sm4.X86.CtrFinal.CtrImpl) =>
    Spec.Sm4.ctrFinalApi.artifact X86.target {
      suffix := c.suffix
      code := Impl.Sm4.X86.Fn.ctrFinal c.name c.code c.words
      verified := Proof.Sm4.X86.Scrub.ctrFinal_scrubbed c
      spSafe := Proof.Sm4.X86.Scrub.ctrFinal_spSafeF c }

public def artifacts : List (Artifact X86.target) := [
  Spec.Sm4.ctrApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.ctr
    verified := Proof.Sm4.X86.AesNiWide.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ctr
    verified := Proof.Sm4.X86.Scrub.ctr_scrubbed }] ++ finals

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.X86
