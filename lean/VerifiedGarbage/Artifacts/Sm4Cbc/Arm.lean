module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Sm4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CBC on ARMv7 -/

namespace VG.Artifacts.Sm4Cbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cbcEncryptChained
    verified := Proof.Sm4.Arm.Fn.cbcEncryptChained },
  Spec.Sm4.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cbcDecryptChained
    verified := Proof.Sm4.Arm.Fn.cbcDecryptChained }]

spec_apis artifacts

end VG.Artifacts.Sm4Cbc.Arm
