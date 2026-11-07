module

public import VerifiedGarbage.Proof.Sm4.AArch64.CtrVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Lit

/-! # SM4-CTR artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 Impl.Sm4.AArch64.ctr
    stack := 3264
    verified := Proof.Sm4.AArch64.ctr_framed },
  Spec.Sm4.ctrFinalApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x4 10 Impl.Sm4.AArch64.ctrFinal
    stack := 3344
    verified := Proof.Sm4.AArch64.CtrFinal.ctrFinal_framed }]

end VG.Artifacts.Sm4Ctr.AArch64
