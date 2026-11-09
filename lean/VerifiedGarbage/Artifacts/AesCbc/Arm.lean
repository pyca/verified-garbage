module

public import VerifiedGarbage.Proof.AesCbc.Arm.Wiped
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.Proof.AesCbc.Arm.Body

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

open VG.Proof.AesCbc.Arm.Wiped

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    code := encrypt
    stack := 32
    verified := encrypt_verified },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    code := decrypt
    stack := 32
    verified := decrypt_verified }]

end VG.Artifacts.AesCbc.Arm
