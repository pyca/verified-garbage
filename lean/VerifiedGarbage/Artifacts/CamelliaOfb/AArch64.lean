module

public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Camellia.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit

/-! # Camellia-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.AArch64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.ofbCode
    verified := Proof.Camellia.AArch64.Residue.ofbCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.ofbCode_noResidue⟩ },
  Spec.Camellia.ofbFinalApi.artifact AArch64.target {
    code := Proof.Camellia.AArch64.Residue.ofbFinalCode
    verified := Proof.Camellia.AArch64.Residue.ofbFinalCode_verified
    residue := some ⟨Proof.Camellia.AArch64.Residue.ofbFinalCode_noResidue⟩ }]

end VG.Artifacts.CamelliaOfb.AArch64
