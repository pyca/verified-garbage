module

public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Blowfish-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cbcEncryptChainedCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Blowfish.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.cbcDecryptChainedCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.BlowfishCbc.AArch64
