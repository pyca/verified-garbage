module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Sm4.X86.AesNiWideScrub
public import VerifiedGarbage.Impl.Sm4.X86.AesNiWideFn
import VerifiedGarbage.Proof.Sm4.X86.CtrLit
import VerifiedGarbage.Proof.Sm4.X86.AesNiWideLit
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.X86

/-! # SM4-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86

/-- `vg_sm4_ctr_final`, with each implementation of `vg_sm4_ctr`'s code. -/
def finals : List Artifact :=
  VG.Proof.Variants.Sm4Ctr.X86.variants.map fun (c : Proof.Sm4.X86.CtrFinal.CtrImpl) =>
    Spec.Sm4.ctrFinalApi.artifact X86.target {
      suffix := c.suffix
      code := Impl.Sm4.X86.Fn.ctrFinal c.name c.code c.words
      verified := Proof.Sm4.X86.Scrub.ctrFinal_scrubbed c
      spSafe := Proof.Sm4.X86.Scrub.ctrFinal_spSafeF c }

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86.target {
    suffix := "_aesni"
    code := Impl.Sm4.X86.AesNiWide.Fn.ctr
    verified := Proof.Sm4.X86.AesNiWide.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ctr
    verified := Proof.Sm4.X86.Scrub.ctr_scrubbed }] ++ finals

end VG.Artifacts.Sm4Ctr.X86
