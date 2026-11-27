module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # CAST5-CFB64 on ARMv7 -/

namespace VG.Artifacts.Cast5Cfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cast5.cfbEncryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbEncrypt
    verified := Proof.Cast5.Arm.Fn.cfbEncrypt },
  Spec.Cast5.cfbDecryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbDecrypt
    verified := Proof.Cast5.Arm.Fn.cfbDecrypt },
  Spec.Cast5.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbEncryptFinal
    verified := Proof.Cast5.Arm.Fn.cfbEncryptFinal },
  Spec.Cast5.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbDecryptFinal
    verified := Proof.Cast5.Arm.Fn.cfbDecryptFinal }]

spec_apis artifacts

end VG.Artifacts.Cast5Cfb.Arm
