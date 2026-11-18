module

public import VerifiedGarbage.Proof.Seed.AArch64.FbVerified
public import VerifiedGarbage.Proof.Seed.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Seed.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.Proof.Seed.AArch64.ModesLit
import VerifiedGarbage.Proof.Seed.AArch64.FbFinalLit

/-! # SEED-CFB128 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.AArch64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cfbEncryptCode
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptCode_verified
    residue := some ⟨Proof.Seed.AArch64.ModesResidue.cfbEncryptCode_noResidue⟩ },
  Spec.Seed.cfbDecryptApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cfbDecryptCode
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptCode_verified
    residue := some ⟨Proof.Seed.AArch64.ModesResidue.cfbDecryptCode_noResidue⟩ },
  Spec.Seed.cfbEncryptFinalApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cfbEncryptFinalCode
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptFinalCode_verified
    residue := some ⟨Proof.Seed.AArch64.ModesResidue.cfbEncryptFinalCode_noResidue⟩ },
  Spec.Seed.cfbDecryptFinalApi.artifact AArch64.target {
    code := Proof.Seed.AArch64.ModesResidue.cfbDecryptFinalCode
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptFinalCode_verified
    residue := some ⟨Proof.Seed.AArch64.ModesResidue.cfbDecryptFinalCode_noResidue⟩ }]

end VG.Artifacts.SeedCfb.AArch64
