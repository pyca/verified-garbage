module

public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-! # SM4-CTR on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Sm4.AArch64.Sm4e.ctr
    verified := Proof.Sm4.AArch64.Sm4e.ctr_framed },
  Spec.Sm4.ctrApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr
    verified := Proof.Sm4.AArch64.ctr_framed }] ++
  Proof.Variants.Sm4Ctr.AArch64.variants.map fun (v : Proof.Sm4.AArch64.CtrFinal.CtrImpl) =>
    Spec.Sm4.ctrFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 (Impl.Sm4.AArch64.ctrFinal v.name v.code)
      verified := Proof.Sm4.AArch64.CtrFinal.ctrFinal_framed v }

end VG.Artifacts.Sm4Ctr.AArch64
