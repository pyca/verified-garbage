module

public import VerifiedGarbage.Proof.Sm4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4-CFB128 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.Arm

def artifacts : List Artifact := [
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

end VG.Artifacts.Sm4Cfb.Arm
