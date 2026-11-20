module

public import VerifiedGarbage.Proof.Sm4.X86.Scrub
public import VerifiedGarbage.Impl.Sm4.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sm4.X86.CtrLit

/-! # SM4-CTR on x86 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.X86

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ctr
    verified := .scrubbed Proof.Sm4.X86.Scrub.ctr_scrubbed },
  Spec.Sm4.ctrFinalApi.artifact X86.target {
    code := Impl.Sm4.X86.Fn.ctrFinal
    verified := .scrubbed Proof.Sm4.X86.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.Sm4Ctr.X86
