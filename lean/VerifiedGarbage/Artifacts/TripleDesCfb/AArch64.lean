module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortCfb

/-! # Triple DES-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.TripleDes.cfbDecryptApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.TripleDes.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.TripleDes.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.TripleDesCfb.AArch64
