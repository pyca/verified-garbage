module

public import VerifiedGarbage.Proof.AesEcb.Arm
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-ECB (NIST SP 800-38A §6.1) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesEcb.Arm

def artifacts : List Artifact := [
  Spec.AesEcb.encryptApi.artifact Arm.target {
    code := Proof.AesEcb.Arm.encrypt
    stack := 24
    verified := Proof.AesEcb.Arm.encrypt_verified },
  Spec.AesEcb.decryptApi.artifact Arm.target {
    code := Proof.AesEcb.Arm.decrypt
    stack := 24
    verified := Proof.AesEcb.Arm.decrypt_verified }]

end VG.Artifacts.AesEcb.Arm
