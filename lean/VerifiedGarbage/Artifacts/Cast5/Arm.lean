module

public import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
public import VerifiedGarbage.Proof.Cast5.Arm.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! CAST5 key expansion and ECB on baseline ARMv7. -/

@[expose] public section

namespace VG.Artifacts.Cast5.Arm

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact Arm.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.Arm.expandKey
    stack := 0
    verified := Proof.Cast5.Arm.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.Arm.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.Arm.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact Arm.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.Arm.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.Arm.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.Arm
