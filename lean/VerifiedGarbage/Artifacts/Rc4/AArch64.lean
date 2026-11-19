module

public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedInit
public import VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply
public import VerifiedGarbage.Proof.Rc4.AArch64.Residue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RC4 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rc4.AArch64

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact AArch64.target {
    code := Proof.Rc4.AArch64.initCleared
    verified := .scrubbed ⟨Proof.Rc4.AArch64.initCleared_verified,
      Proof.Rc4.AArch64.initCleared_noResidue _⟩ },
  Spec.Rc4.applyApi.artifact AArch64.target {
    code := Proof.Rc4.AArch64.applyCleared
    verified := .scrubbed ⟨Proof.Rc4.AArch64.applyCleared_verified,
      Proof.Rc4.AArch64.applyCleared_noResidue⟩ }]

end VG.Artifacts.Rc4.AArch64
