module

public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit

/-! # Blowfish-OFB on AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.ofbCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.ofbCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.ofbCode_noResidue⟩ },
  Spec.Blowfish.ofbFinalApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.ModesResidue.ofbFinalCode
    verified := .scrubbed ⟨Proof.Blowfish.AArch64.ModesResidue.ofbFinalCode_verified,
      Proof.Blowfish.AArch64.ModesResidue.ofbFinalCode_noResidue⟩ }]

end VG.Artifacts.BlowfishOfb.AArch64
