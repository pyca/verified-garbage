module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit

/-! # Blowfish-CFB64 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cfbEncryptCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cfbEncryptCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.Blowfish.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cfbDecryptCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cfbDecryptCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.Blowfish.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cfbEncryptFinalCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Blowfish.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cfbDecryptFinalCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.BlowfishCfb.AArch64
