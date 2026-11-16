module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM4 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Sm4e.expandKey
    verified := Proof.Sm4.AArch64.Sm4e.expandKey_verified },
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Serial.expandKey
    verified := Proof.Sm4.AArch64.Serial.expandKey_verified },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Sm4e.ecb .encrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecb_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Sm4e.ecb .decrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecb_verified .decrypt },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.ecbFew .encrypt Proof.Sm4.AArch64.ecbAnyFramed
    verified := Proof.Sm4.AArch64.ecbFew_verified .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.ecbFew .decrypt Proof.Sm4.AArch64.ecbAnyFramed
    verified := Proof.Sm4.AArch64.ecbFew_verified .decrypt }]

end VG.Artifacts.Sm4.AArch64
