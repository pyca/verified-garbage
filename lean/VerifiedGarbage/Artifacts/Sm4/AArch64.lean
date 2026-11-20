module

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
    verified := .scrubbed ⟨Proof.Sm4.AArch64.Sm4e.expandKey_verified,
      Proof.Sm4.AArch64.Sm4e.expandKey_noResidue _⟩ },
  Spec.Sm4.expandKeyApi.artifact AArch64.target {
    code := Impl.Sm4.AArch64.Serial.Fn.expandKey
    verified := .scrubbed Proof.Sm4.AArch64.CtrScrub.expandKey },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.Sm4e.ecbCleared .encrypt
    verified := .scrubbed ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .encrypt,
      Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .encrypt⟩ },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.Sm4e.ecbCleared .decrypt
    verified := .scrubbed ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .decrypt,
      Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .decrypt⟩ },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode
    verified := .scrubbed ⟨Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_verified,
      Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_noResidue⟩ },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode
    verified := .scrubbed ⟨Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_verified,
      Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_noResidue⟩ }]

end VG.Artifacts.Sm4.AArch64
