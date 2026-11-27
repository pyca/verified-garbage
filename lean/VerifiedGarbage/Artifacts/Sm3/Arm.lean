module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM3 (GB/T 32905-2016) on ARMv7 -/

namespace VG.Artifacts.Sm3.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm3.initApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.init
    verified := Proof.Sm3.Arm.Fn.init },
  Spec.Sm3.updateApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.update
    verified := Proof.Sm3.Arm.Fn.update },
  Spec.Sm3.finalizeApi.artifact Arm.target {
    code := Impl.Sm3.Arm.Fn.finalize
    verified := Proof.Sm3.Arm.Fn.finalize }]

spec_apis artifacts

end VG.Artifacts.Sm3.Arm
