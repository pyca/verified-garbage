module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Ctr
public import VerifiedGarbage.Spec.Camellia.CtrFinal
import VerifiedGarbage.Proof.Camellia.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CTR on ARMv7 -/

namespace VG.Artifacts.CamelliaCtr.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Camellia.ctrApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ctr
    verified := Proof.Camellia.Arm.Fn.ctr },
  Spec.Camellia.ctrFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ctrFinal
    verified := Proof.Camellia.Arm.Fn.ctrFinal }]

spec_apis artifacts

end VG.Artifacts.CamelliaCtr.Arm
