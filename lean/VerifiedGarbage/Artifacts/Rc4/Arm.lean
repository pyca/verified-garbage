module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Rc4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC4 on ARMv7 -/

namespace VG.Artifacts.Rc4.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Rc4.initApi.artifact Arm.target {
    code := Impl.Rc4.Arm.Fn.init
    verified := Proof.Rc4.Arm.Fn.init },
  Spec.Rc4.applyApi.artifact Arm.target {
    code := Impl.Rc4.Arm.Fn.apply
    verified := Proof.Rc4.Arm.Fn.apply }]

spec_apis artifacts

end VG.Artifacts.Rc4.Arm
