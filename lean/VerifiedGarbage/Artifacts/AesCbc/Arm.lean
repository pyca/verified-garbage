module

public import VerifiedGarbage.Proof.AesCbc.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCbc.Arm.Body

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

open VG.Proof.AesCbc.Arm

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    code := Impl.AesCbc.Arm.encrypt
    stack := 8
    verified := encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    code := Impl.AesCbc.Arm.decrypt
    stack := 8
    verified := decrypt_verified }]

end VG.Artifacts.AesCbc.Arm
