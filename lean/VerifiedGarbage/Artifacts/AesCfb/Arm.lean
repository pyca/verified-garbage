module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Spec.Cfb.Final
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB128 (NIST SP 800-38A §6.3) on ARMv7 -/

namespace VG.Artifacts.AesCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cfb.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbEncrypt
    verified := Proof.Aes.Arm.Fn.cfbEncrypt },
  Spec.Cfb.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbDecrypt
    verified := Proof.Aes.Arm.Fn.cfbDecrypt },
  Spec.Cfb.aesEncryptFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbEncryptFinal
    verified := Proof.Aes.Arm.Fn.cfbEncryptFinal },
  Spec.Cfb.aesDecryptFinalApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfbDecryptFinal
    verified := Proof.Aes.Arm.Fn.cfbDecryptFinal }]

spec_apis artifacts

end VG.Artifacts.AesCfb.Arm
