module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2b (RFC 7693) on ARMv7 -/

namespace VG.Artifacts.Blake2b.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Blake2.initBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.initB
    verified := Proof.Blake2.Arm.Fn.initB },
  Spec.Blake2.updateBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.updateB
    verified := Proof.Blake2.Arm.Fn.updateB },
  Spec.Blake2.finalizeBApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.finalizeB
    verified := Proof.Blake2.Arm.Fn.finalizeB }]

spec_apis artifacts

end VG.Artifacts.Blake2b.Arm
