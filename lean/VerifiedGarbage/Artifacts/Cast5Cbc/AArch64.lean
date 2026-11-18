module

public import VerifiedGarbage.Proof.Cast5.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.TblModesVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Cast5.AArch64.TblLit

/-! # CAST5-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cbc.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.cbcEncryptChainedApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode
    verified := Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cbcEncryptChainedCode_noResidue⟩ },
  Spec.Cast5.cbcDecryptChainedApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode
    verified := Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_verified
    residue := some ⟨Proof.Cast5.AArch64.ModesResidue.cbcDecryptChainedCode_noResidue⟩ }]

end VG.Artifacts.Cast5Cbc.AArch64
