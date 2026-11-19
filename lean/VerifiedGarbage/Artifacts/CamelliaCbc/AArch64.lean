module

public import VerifiedGarbage.Proof.Camellia.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Camellia-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cbcEncryptChainedCode
    verified := .scrubbed ⟨Proof.Camellia.AArch64.Residue.cbcEncryptChainedCode_verified,
      Proof.Camellia.AArch64.Residue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Camellia.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.cbcDecryptChainedCode
    verified := .scrubbed ⟨Proof.Camellia.AArch64.Residue.cbcDecryptChainedCode_verified,
      Proof.Camellia.AArch64.Residue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.CamelliaCbc.AArch64
