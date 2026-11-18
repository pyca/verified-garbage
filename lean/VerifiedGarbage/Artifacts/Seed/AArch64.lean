module

public import VerifiedGarbage.Proof.Seed.AArch64.Frame
public import VerifiedGarbage.Proof.Seed.AArch64.EcbCall
public import VerifiedGarbage.Proof.Seed.AArch64.Verified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # SEED on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Seed.AArch64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.expandKeyCode
    verified := Proof.Seed.AArch64.ModesResidue.expandKeyCode_verified
    residue := some ⟨Proof.Seed.AArch64.ModesResidue.expandKeyCode_noResidue⟩ },
  Spec.Seed.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x3 182 Impl.Seed.AArch64.ecbEncrypt
    verified := Proof.Seed.AArch64.ecbFew_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 1456 .x3 182 Impl.Seed.AArch64.ecbDecrypt
    verified := Proof.Seed.AArch64.ecbFew_framed .decrypt }]

end VG.Artifacts.Seed.AArch64
