module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Ctr
public import VerifiedGarbage.Spec.Sm4.CtrFinal
import VerifiedGarbage.Proof.Sm4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CTR on ARMv7 -/

namespace VG.Artifacts.Sm4Ctr.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.ctrApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ctr
    verified := Proof.Sm4.Arm.Fn.ctr },
  Spec.Sm4.ctrFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ctrFinal
    verified := Proof.Sm4.Arm.Fn.ctrFinal }]

spec_apis artifacts

end VG.Artifacts.Sm4Ctr.Arm
