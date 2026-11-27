module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Camellia.Cfb
public import VerifiedGarbage.Spec.Camellia.CfbFinal
import VerifiedGarbage.Proof.Camellia.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Camellia-CFB128 on ARMv7 -/

namespace VG.Artifacts.CamelliaCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Camellia.cfbEncryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbEncrypt
    verified := Proof.Camellia.Arm.Fn.cfbEncrypt },
  Spec.Camellia.cfbDecryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbDecrypt
    verified := Proof.Camellia.Arm.Fn.cfbDecrypt },
  Spec.Camellia.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbEncryptFinal
    verified := Proof.Camellia.Arm.Fn.cfbEncryptFinal },
  Spec.Camellia.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbDecryptFinal
    verified := Proof.Camellia.Arm.Fn.cfbDecryptFinal }]

spec_apis artifacts

end VG.Artifacts.CamelliaCfb.Arm
