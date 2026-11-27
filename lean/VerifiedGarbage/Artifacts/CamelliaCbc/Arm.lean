module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cbc
import VerifiedGarbage.Proof.Camellia.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CBC on ARMv7 -/

namespace VG.Artifacts.CamelliaCbc.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Camellia.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cbcEncrypt
    verified := Proof.Camellia.Arm.Fn.cbcEncrypt },
  Spec.Camellia.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cbcDecrypt
    verified := Proof.Camellia.Arm.Fn.cbcDecrypt }]

spec_apis artifacts

end VG.Artifacts.CamelliaCbc.Arm
