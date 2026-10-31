module

public import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # CAST5 key expansion and ECB on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact AArch64.target {
    consts := Impl.Cast5.keyConsts
    code := Impl.Cast5.AArch64.expandKey
    stack := 0
    verified := Proof.Cast5.AArch64.expandKey_verified },
  Spec.Cast5.ecbEncryptApi.artifact AArch64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbEncrypt
    stack := 0
    verified := Proof.Cast5.AArch64.ecbEncrypt_verified },
  Spec.Cast5.ecbDecryptApi.artifact AArch64.target {
    consts := Impl.Cast5.ecbConsts
    code := Impl.Cast5.AArch64.ecbDecrypt
    stack := 0
    verified := Proof.Cast5.AArch64.ecbDecrypt_verified }]

end VG.Artifacts.Cast5.AArch64
