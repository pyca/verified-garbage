module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.Residue
public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Blowfish on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.expandKeyCleared
    verified := Proof.Blowfish.AArch64.expandKeyCleared_verified
    residue := some ⟨Proof.Blowfish.AArch64.expandKeyCleared_noResidue⟩ },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.ecbEncryptCode
    verified := Proof.Blowfish.AArch64.ModesResidue.ecbEncryptCode_verified
    residue := some ⟨Proof.Blowfish.AArch64.ModesResidue.ecbEncryptCode_noResidue⟩ },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.ecbDecryptCode
    verified := Proof.Blowfish.AArch64.ModesResidue.ecbDecryptCode_verified
    residue := some ⟨Proof.Blowfish.AArch64.ModesResidue.ecbDecryptCode_noResidue⟩ }]

end VG.Artifacts.Blowfish.AArch64
