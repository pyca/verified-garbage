module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Blake2.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # BLAKE2s (RFC 7693) on ARMv7 -/

namespace VG.Artifacts.Blake2s.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Blake2.initSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.initS
    verified := Proof.Blake2.Arm.Fn.initS },
  Spec.Blake2.updateSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.updateS
    verified := Proof.Blake2.Arm.Fn.updateS },
  Spec.Blake2.finalizeSApi.artifact Arm.target {
    code := Impl.Blake2.Arm.Fn.finalizeS
    verified := Proof.Blake2.Arm.Fn.finalizeS }]

spec_apis artifacts

end VG.Artifacts.Blake2s.Arm
