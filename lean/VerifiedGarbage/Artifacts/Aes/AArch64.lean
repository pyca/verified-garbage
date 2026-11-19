module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.Frame
public import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.KeyResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES (FIPS 197) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    code := Proof.Aes.AArch64.KeyResidue.expandKeyCode
    verified := .scrubbed ⟨Proof.Aes.AArch64.KeyResidue.expandKeyCode_verified,
      Proof.Aes.AArch64.KeyResidue.expandKeyCode_noResidue⟩ },
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    suffix := "_aes"
    code := Proof.Aes.AArch64.KeyResidue.expandKeyAesCode
    verified := .scrubbed ⟨Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_verified,
      Proof.Aes.AArch64.KeyResidue.expandKeyAesCode_noResidue⟩ }]

end VG.Artifacts.Aes.AArch64
