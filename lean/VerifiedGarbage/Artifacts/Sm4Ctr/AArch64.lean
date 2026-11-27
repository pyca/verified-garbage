module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.AArch64.CtrFinal
import VerifiedGarbage.Proof.Variants.Sm4Ctr.AArch64
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
import VerifiedGarbage.Proof.Sm4.AArch64.CtrScrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on AArch64 -/

namespace VG.Artifacts.Sm4Ctr.AArch64

public def artifacts : List (Artifact AArch64.target) := [
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

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.AArch64
