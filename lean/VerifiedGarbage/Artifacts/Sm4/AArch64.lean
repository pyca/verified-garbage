module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Key
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
    verified := Proof.Sm4.AArch64.Sm4e.expandKey_verified
    residue := some ⟨Proof.Sm4.AArch64.Sm4e.expandKey_noResidue _⟩ },
  Spec.Sm4.expandKeyApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    code := Impl.Sm4.AArch64.Serial.expandKey
    verified := Proof.Sm4.AArch64.Serial.expandKey_verified }
      ⟨[.x6, .x7, .x8, .x9, .x10, .x11, .x15],
       [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26,
       .v27, .v28, .v29, .v30, .v31],
       []⟩ Proof.Sm4.AArch64.CtrScrub.expandKeyOk),
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.Sm4e.ecbCleared .encrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .encrypt
    residue := some ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .encrypt⟩ },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.Sm4e.ecbCleared .decrypt
    verified := Proof.Sm4.AArch64.Sm4e.ecbCleared_verified .decrypt
    residue := some ⟨Proof.Sm4.AArch64.Sm4e.ecbCleared_noResidue _ .decrypt⟩ },
  Spec.Sm4.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode
    verified := Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_verified
    residue := some ⟨Proof.Sm4.AArch64.EcbResidue.ecbEncryptCode_noResidue⟩ },
  Spec.Sm4.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode
    verified := Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_verified
    residue := some ⟨Proof.Sm4.AArch64.EcbResidue.ecbDecryptCode_noResidue⟩ }]

end VG.Artifacts.Sm4.AArch64
