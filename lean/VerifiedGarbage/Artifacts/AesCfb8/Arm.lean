module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.Aes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CFB8 (NIST SP 800-38A §6.3) on ARMv7 -/

namespace VG.Artifacts.AesCfb8.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cfb8.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfb8Encrypt
    verified := Proof.Aes.Arm.Fn.cfb8Encrypt },
  Spec.Cfb8.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cfb8Decrypt
    verified := Proof.Aes.Arm.Fn.cfb8Decrypt }]

spec_apis artifacts

end VG.Artifacts.AesCfb8.Arm
