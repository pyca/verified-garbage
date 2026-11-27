module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rc2.Contract
import VerifiedGarbage.Proof.Rc2.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RC2 on ARMv7 -/

namespace VG.Artifacts.Rc2.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Rc2.cbcInitApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcInit
    verified := Proof.Rc2.Arm.Fn.cbcInit },
  Spec.Rc2.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcEncryptChained
    verified := Proof.Rc2.Arm.Fn.cbcEncryptChained },
  Spec.Rc2.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Fn.cbcDecryptChained
    verified := Proof.Rc2.Arm.Fn.cbcDecryptChained }]

spec_apis artifacts

end VG.Artifacts.Rc2.Arm
