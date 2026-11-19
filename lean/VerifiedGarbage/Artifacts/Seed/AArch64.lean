module

public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Seed.AArch64.EcbResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SEED on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.expandKeyCode
    verified := .scrubbed ⟨Proof.Seed.AArch64.ModesResidue.expandKeyCode_verified,
      Proof.Seed.AArch64.ModesResidue.expandKeyCode_noResidue⟩ },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.EcbResidue.ecbEncryptCode
    verified := .scrubbed ⟨Proof.Seed.AArch64.EcbResidue.ecbEncryptCode_verified,
      Proof.Seed.AArch64.EcbResidue.ecbEncryptCode_noResidue⟩ },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.EcbResidue.ecbDecryptCode
    verified := .scrubbed ⟨Proof.Seed.AArch64.EcbResidue.ecbDecryptCode_verified,
      Proof.Seed.AArch64.EcbResidue.ecbDecryptCode_noResidue⟩ }]

end VG.Artifacts.Seed.AArch64
