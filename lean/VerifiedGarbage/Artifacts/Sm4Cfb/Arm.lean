module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.CfbFinal
import VerifiedGarbage.Proof.Sm4.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4-CFB128 on ARMv7 -/

namespace VG.Artifacts.Sm4Cfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.cfbEncryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cfbEncrypt
    verified := Proof.Sm4.Arm.Fn.cfbEncrypt },
  Spec.Sm4.cfbDecryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cfbDecrypt
    verified := Proof.Sm4.Arm.Fn.cfbDecrypt },
  Spec.Sm4.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cfbEncryptFinal
    verified := Proof.Sm4.Arm.Fn.cfbEncryptFinal },
  Spec.Sm4.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.cfbDecryptFinal
    verified := Proof.Sm4.Arm.Fn.cfbDecryptFinal }]

spec_apis artifacts

end VG.Artifacts.Sm4Cfb.Arm
