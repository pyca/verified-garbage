module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Contract
import VerifiedGarbage.Proof.Camellia.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia on ARMv7 -/

namespace VG.Artifacts.Camellia.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Camellia.expandKeyApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.expandKey
    verified := Proof.Camellia.Arm.Fn.expandKey },
  Spec.Camellia.ecbEncryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ecbEncrypt
    verified := Proof.Camellia.Arm.Fn.ecbEncrypt },
  Spec.Camellia.ecbDecryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ecbDecrypt
    verified := Proof.Camellia.Arm.Fn.ecbDecrypt }]

spec_apis artifacts

end VG.Artifacts.Camellia.Arm
