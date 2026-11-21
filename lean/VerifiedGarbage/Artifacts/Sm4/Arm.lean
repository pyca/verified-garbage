module

public import VerifiedGarbage.Proof.Sm4.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # SM4 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4.Arm

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.expandKey
    verified := Proof.Sm4.Arm.Fn.expandKey },
  Spec.Sm4.ecbEncryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ecbEncrypt
    verified := Proof.Sm4.Arm.Fn.ecbEncrypt },
  Spec.Sm4.ecbDecryptApi.artifact Arm.target {
    code := Impl.Sm4.Arm.Fn.ecbDecrypt
    verified := Proof.Sm4.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.Sm4.Arm
