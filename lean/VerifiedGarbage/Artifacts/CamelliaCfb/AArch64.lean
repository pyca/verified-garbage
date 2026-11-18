module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-CFB128 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cfbEncryptCode
    verified := Proof.Camellia.AArch64.Residue.cfbEncryptCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.cfbEncryptCode_noResidue⟩ },
  Spec.Camellia.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cfbDecryptCode
    verified := Proof.Camellia.AArch64.Residue.cfbDecryptCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.cfbDecryptCode_noResidue⟩ },
  Spec.Camellia.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cfbEncryptFinalCode
    verified := Proof.Camellia.AArch64.Residue.cfbEncryptFinalCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Camellia.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cfbDecryptFinalCode
    verified := Proof.Camellia.AArch64.Residue.cfbDecryptFinalCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.CamelliaCfb.AArch64
