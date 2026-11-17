module

public import VerifiedGarbage.Proof.Idea.AArch64.Invert
public import VerifiedGarbage.Proof.Idea.AArch64.Ecb
public import VerifiedGarbage.Proof.Idea.AArch64.Key
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Idea.AArch64.Residue

/-! # IDEA on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Idea.AArch64

def artifacts : List Artifact := [
  Spec.Idea.expandKeyApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.Residue.expandKeyCleared
    verified := Proof.Idea.AArch64.Residue.expandKeyCleared_verified
    residue := some ⟨Proof.Idea.AArch64.Residue.expandKeyCleared_noResidue _⟩ },
  Spec.Idea.invertKeyApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.Residue.invertKeyCleared
    verified := Proof.Idea.AArch64.Residue.invertKeyCleared_verified
    residue := some ⟨Proof.Idea.AArch64.Residue.invertKeyCleared_noResidue _⟩ },
  Spec.Idea.ecbApi.artifact AArch64.target {
    code := Proof.Idea.AArch64.Residue.ecbCleared
    verified := Proof.Idea.AArch64.Residue.ecbCleared_verified
    residue := some ⟨Proof.Idea.AArch64.Residue.ecbCleared_noResidue _⟩ }]

end VG.Artifacts.Idea.AArch64
