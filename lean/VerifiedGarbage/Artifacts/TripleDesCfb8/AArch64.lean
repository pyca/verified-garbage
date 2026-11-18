module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
public import VerifiedGarbage.Proof.TripleDes.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Triple DES-CFB8 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.AArch64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfb8EncryptCode_noResidue⟩ },
  Spec.TripleDes.cfb8DecryptApi.artifact AArch64.target {
    code := Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode
    verified := Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_verified
    residue := some ⟨Proof.TripleDes.AArch64.ModesResidue.cfb8DecryptCode_noResidue⟩ }]

end VG.Artifacts.TripleDesCfb8.AArch64
