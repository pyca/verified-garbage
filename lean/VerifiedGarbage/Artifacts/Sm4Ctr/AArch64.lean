module

public import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
public import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrScrub

/-! # SM4-CTR on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Ctr.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.ctrApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ctrSm4
    verified := Proof.Sm4.AArch64.CtrScrub.ctrSm4 },
  Spec.Sm4.ctrApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ctr
    verified := Proof.Sm4.AArch64.CtrScrub.ctr }] ++
  Proof.Variants.Sm4Ctr.AArch64.variants.map fun (v : Proof.Sm4.AArch64.CtrFinal.CtrImpl) =>
    Spec.Sm4.ctrFinalApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Sm4.AArch64.Fn.ctrFinal v.clear v.name v.code
      verified := Proof.Sm4.AArch64.CtrScrub.ctrFinal v }

end VG.Artifacts.Sm4Ctr.AArch64
