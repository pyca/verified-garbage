module

public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit

/-! # SM4-CFB128 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptSm4Code_noResidue⟩ },
  Spec.Sm4.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptSm4Code_noResidue⟩ },
  Spec.Sm4.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.Sm4.cfbEncryptFinalApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalSm4Code_noResidue⟩ },
  Spec.Sm4.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Sm4.cfbDecryptFinalApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalSm4Code_noResidue⟩ },
  Spec.Sm4.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_verified
    residue := some ⟨Proof.Sm4.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.Sm4Cfb.AArch64
