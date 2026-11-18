module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit
public import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # CAST5-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode
    verified := Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.Cast5.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode
    verified := Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.Cast5.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Cast5.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.Cast5Cfb.AArch64
