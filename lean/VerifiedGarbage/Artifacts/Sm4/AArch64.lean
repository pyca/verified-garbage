module

public import VerifiedGarbage.Impl.Sm4.AArch64.Fn
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
public import VerifiedGarbage.Proof.Sm4.AArch64.Verified
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
public import VerifiedGarbage.Proof.Sm4.AArch64.EcbResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Sm4.AArch64.CtrScrub
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM4 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Sm4e.expandKey
    verified := .scrubbed Proof.Sm4.AArch64.Sm4e.expandKey_scrubbed },
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Serial.Fn.expandKey
    verified := .scrubbed Proof.Sm4.AArch64.CtrScrub.expandKey },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ecb .encrypt
    verified := .scrubbed Proof.Sm4.AArch64.Sm4e.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ecb .decrypt
    verified := .scrubbed Proof.Sm4.AArch64.Sm4e.ecbDecrypt_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ecbEncrypt
    verified := .scrubbed Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ecbDecrypt
    verified := .scrubbed Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_scrubbed }]

end VG.Artifacts.Sm4.AArch64
