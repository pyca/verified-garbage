module

public import VerifiedGarbage.Proof.AesXts.Arm.Verified
public import VerifiedGarbage.Proof.AesXts.Arm.Unit.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # XTS-AES (IEEE Std 1619-2007, NIST SP 800-38E) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesXts.Arm

open VG.Proof.AesXts.Arm

def artifacts : List Artifact := [
  Spec.Xts.aesEncryptUnitApi.artifact Arm.target {
    code := Impl.AesXts.ArmUnit.encrypt
    stack := 16
    verified := Unit.encrypt_verified },
  Spec.Xts.aesDecryptUnitApi.artifact Arm.target {
    code := Impl.AesXts.ArmUnit.decrypt
    stack := 16
    verified := Unit.decrypt_verified }]

end VG.Artifacts.AesXts.Arm
