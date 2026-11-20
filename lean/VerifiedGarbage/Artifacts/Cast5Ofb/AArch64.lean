module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Cast5.AArch64.FbResidue
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # CAST5-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.AArch64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.FbResidue.ofbCode
    verified := .scrubbed Proof.Cast5.AArch64.FbResidue.ofbCode_scrubbed },
  Spec.Cast5.ofbFinalApi.artifact AArch64.target {
    code := Proof.Cast5.AArch64.FbResidue.ofbFinalCode
    verified := .scrubbed Proof.Cast5.AArch64.FbResidue.ofbFinalCode_scrubbed }]

end VG.Artifacts.Cast5Ofb.AArch64
