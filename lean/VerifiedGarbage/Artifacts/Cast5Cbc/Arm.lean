module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Proof.Cast5.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CBC on ARMv7 -/

namespace VG.Artifacts.Cast5Cbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cast5.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cbcEncryptChained
    verified := Proof.Cast5.Arm.Fn.cbcEncryptChained },
  Spec.Cast5.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cbcDecryptChained
    verified := Proof.Cast5.Arm.Fn.cbcDecryptChained }]

spec_apis artifacts

end VG.Artifacts.Cast5Cbc.Arm
