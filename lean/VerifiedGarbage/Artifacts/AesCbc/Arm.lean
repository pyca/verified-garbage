module

public import VerifiedGarbage.Proof.Aes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # AES-CBC (NIST SP 800-38A §6.2) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.AesCbc.Arm

def artifacts : List Artifact := [
  Spec.Cbc.aesEncryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcEncrypt
    verified := .scrubbed Proof.Aes.Arm.Fn.cbcEncrypt },
  Spec.Cbc.aesDecryptApi.artifact Arm.target {
    code := Impl.Aes.Arm.Fn.cbcDecrypt
    verified := .scrubbed Proof.Aes.Arm.Fn.cbcDecrypt }]

end VG.Artifacts.AesCbc.Arm
