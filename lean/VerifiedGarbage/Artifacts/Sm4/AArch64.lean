module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Contract
import VerifiedGarbage.Impl.Sm4.AArch64.Fn
import VerifiedGarbage.Proof.Sm4.AArch64.EcbCall
import VerifiedGarbage.Proof.Sm4.AArch64.Verified
import VerifiedGarbage.Proof.Sm4.AArch64.PreparedVerified
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Ecb
import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Key
import VerifiedGarbage.Proof.Sm4.AArch64.EcbResidue
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.AArch64.CtrScrub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM4 on AArch64 -/

namespace VG.Artifacts.Sm4.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Sm4e.expandKey
    verified := Proof.Sm4.AArch64.Sm4e.expandKey_scrubbed },
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Serial.Fn.expandKey
    verified := Proof.Sm4.AArch64.CtrScrub.expandKey },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ecb .encrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecbEncrypt_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Impl.Sm4.AArch64.Fn.ecb .decrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecbDecrypt_scrubbed },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ecbEncrypt
    verified := Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_scrubbed },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Fn.ecbDecrypt
    verified := Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm4.AArch64
