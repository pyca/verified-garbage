module

public import VerifiedGarbage.Proof.Sm4.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Chained
public import VerifiedGarbage.Proof.Sm4.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SM4-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code
    verified := .scrubbed ⟨Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_verified,
      Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedSm4Code_noResidue⟩ },
  Spec.Sm4.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode
    verified := .scrubbed ⟨Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_verified,
      Proof.Sm4.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    suffix := "_sm4"
    code := Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code
    verified := .scrubbed ⟨Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_verified,
      Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedSm4Code_noResidue⟩ },
  Spec.Sm4.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode
    verified := .scrubbed ⟨Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_verified,
      Proof.Sm4.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.Sm4Cbc.AArch64
