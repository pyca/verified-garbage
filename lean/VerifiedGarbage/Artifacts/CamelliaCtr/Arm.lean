module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CTR on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCtr.Arm

def artifacts : List Artifact := [
  Spec.Camellia.ctrApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ctr
    verified := .scrubbed Proof.Camellia.Arm.Fn.ctr },
  Spec.Camellia.ctrFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ctrFinal
    verified := .scrubbed Proof.Camellia.Arm.Fn.ctrFinal }]

end VG.Artifacts.CamelliaCtr.Arm
