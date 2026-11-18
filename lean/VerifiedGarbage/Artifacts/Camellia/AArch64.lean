module

public import VerifiedGarbage.Proof.Camellia.AArch64.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
public import VerifiedGarbage.Proof.Camellia.AArch64.Lit
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Camellia on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Camellia.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.expandKeyCode
    verified := Proof.Camellia.AArch64.Residue.expandKeyCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.expandKeyCode_noResidue⟩ },
  Spec.Camellia.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.ecbEncryptCode
    verified := Proof.Camellia.AArch64.Residue.ecbEncryptCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.ecbEncryptCode_noResidue⟩ },
  Spec.Camellia.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.ecbDecryptCode
    verified := Proof.Camellia.AArch64.Residue.ecbDecryptCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.ecbDecryptCode_noResidue⟩ }]

end VG.Artifacts.Camellia.AArch64
