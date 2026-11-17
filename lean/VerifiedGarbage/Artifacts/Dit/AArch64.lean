module

public import VerifiedGarbage.Proof.Dit.AArch64
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Data independent timing (FEAT_DIT) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Dit.AArch64

def artifacts : List Artifact := [
  Spec.Dit.enterApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.enter
    verified := Proof.Dit.AArch64.enter_verified
    residue := some ⟨Proof.Dit.AArch64.enter_noResidue _ _⟩ },
  Spec.Dit.enterApi.artifact AArch64.target {
    suffix := "_dsb"
    code := Impl.Dit.AArch64.enterDsb
    verified := Proof.Dit.AArch64.enterDsb_verified
    residue := some ⟨Proof.Dit.AArch64.enterDsb_noResidue _ _⟩ },
  Spec.Dit.enterApi.artifact AArch64.target {
    suffix := "_sb"
    code := Impl.Dit.AArch64.enterSb
    verified := Proof.Dit.AArch64.enterSb_verified
    residue := some ⟨Proof.Dit.AArch64.enterSb_noResidue _ _⟩ },
  Spec.Dit.clearApi.artifact AArch64.target {
    code := Impl.Dit.AArch64.clear
    verified := Proof.Dit.AArch64.clear_verified
    residue := some ⟨Proof.Dit.AArch64.clear_noResidue _ _⟩ }]

end VG.Artifacts.Dit.AArch64
