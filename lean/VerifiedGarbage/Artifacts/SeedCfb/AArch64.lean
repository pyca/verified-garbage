module

public import VerifiedGarbage.Impl.Seed.AArch64.Fn
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
    code := Impl.Seed.AArch64.Fn.cfbEncrypt
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptCode_scrubbed },
  Spec.Seed.cfbDecryptApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbDecrypt
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptCode_scrubbed },
  Spec.Seed.cfbEncryptFinalApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbEncryptFinal
    verified := Proof.Seed.AArch64.ModesResidue.cfbEncryptFinalCode_scrubbed },
  Spec.Seed.cfbDecryptFinalApi.artifact AArch64.target {
    code := Impl.Seed.AArch64.Fn.cfbDecryptFinal
    verified := Proof.Seed.AArch64.ModesResidue.cfbDecryptFinalCode_scrubbed }]

end VG.Artifacts.SeedCfb.AArch64
